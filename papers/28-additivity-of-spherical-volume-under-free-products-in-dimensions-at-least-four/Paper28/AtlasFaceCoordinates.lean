import Paper28.SphericalRealizationCharts

/-! Actual barycentric coordinates on retained faces, their carrier
membership and uniqueness from the native simplicial-complex independence.
No geometric embedding or integration uniqueness theorem is assumed. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  (A : FullSubcomplexBarycentricAtlas K V Idx)

theorem supportedSimplex_sum (F : Finset V) (t : stdSimplex ℝ V)
    (hZero : ∀ v, v ∉ F → t.val v = 0) : ∑ v ∈ F, t.val v = 1 := by
  calc
    _ = ∑ v, t.val v := Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => hZero v hv)
    _ = 1 := t.property.2

theorem supportedSimplex_nonempty (F : Finset V) (t : stdSimplex ℝ V)
    (hZero : ∀ v, v ∉ F → t.val v = 0) : F.Nonempty := by
  by_contra h
  have he := supportedSimplex_sum F t hZero
  rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.sum_empty] at he
  exact zero_ne_one he

theorem supportedSimplex_vector {E : Type*} [AddCommGroup E] [Module ℝ E]
    (F : Finset V) (t : stdSimplex ℝ V) (q : V → E)
    (hZero : ∀ v, v ∉ F → t.val v = 0) :
    ∑ v ∈ F, t.val v • q v = ∑ v, t.val v • q v :=
  Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by rw [hZero v hv,zero_smul])

theorem atlasFacePoint_mem (j : Idx) (t : stdSimplex ℝ V)
    (hZero : ∀ v, v ∉ A.cells j ∩ A.selected → t.val v = 0) :
    (∑ v, t.val v • A.vertex v) ∈ K.complex.space := by
  let F := A.cells j ∩ A.selected
  have hF := A.full_face j (supportedSimplex_nonempty F t hZero)
  apply K.complex.convexHull_subset_space hF
  rw [← supportedSimplex_vector F t A.vertex hZero]
  exact (convex_convexHull ℝ _).sum_mem (fun v _ => t.property.1 v)
    (supportedSimplex_sum F t hZero)
    (fun v hv => subset_convexHull ℝ _ (Finset.mem_image.mpr ⟨v,hv,rfl⟩))

theorem atlasFace_affineIndependent (hA : Function.Injective A.vertex) (j : Idx)
    (hF : (A.cells j ∩ A.selected).Nonempty) :
    AffineIndependent ℝ (fun v : {v : V // v ∈ A.cells j ∩ A.selected} => A.vertex v.val) := by
  let F := A.cells j ∩ A.selected
  let e : F ↪ (F.image A.vertex) :=
    ⟨fun v => ⟨A.vertex v.val,Finset.mem_image.mpr ⟨v.val,v.property,rfl⟩⟩,
      fun _ _ he => Subtype.ext (hA (congrArg Subtype.val he))⟩
  exact (K.complex.indep (A.full_face j hF)).comp_embedding e

theorem atlasFace_coordinates_unique (hA : Function.Injective A.vertex) (j : Idx)
    (t s : stdSimplex ℝ V)
    (ht : ∀ v, v ∉ A.cells j ∩ A.selected → t.val v = 0)
    (hs : ∀ v, v ∉ A.cells j ∩ A.selected → s.val v = 0)
    (he : (∑ v, t.val v • A.vertex v) = ∑ v, s.val v • A.vertex v) : t = s := by
  let F := A.cells j ∩ A.selected
  have hF : F.Nonempty := supportedSimplex_nonempty F t ht
  have hsum : (∑ v ∈ F, t.val v) = ∑ v ∈ F, s.val v :=
    (supportedSimplex_sum F t ht).trans (supportedSimplex_sum F s hs).symm
  have hvec : (∑ v ∈ F, t.val v • A.vertex v) = ∑ v ∈ F, s.val v • A.vertex v :=
    (supportedSimplex_vector F t A.vertex ht).trans (he.trans (supportedSimplex_vector F s A.vertex hs).symm)
  have hu : ∀ v : F, t.val v.val = s.val v.val := by
    intro v
    apply (atlasFace_affineIndependent A hA j hF).eq_of_sum_eq_sum
      (s := Finset.univ) (w₁ := fun v => t.val v.val) (w₂ := fun v => s.val v.val)
      ?_ ?_ v (Finset.mem_univ _)
    · change (∑ v ∈ F.attach, t.val v.val) = ∑ v ∈ F.attach, s.val v.val
      rw [Finset.sum_attach,Finset.sum_attach]
      exact hsum
    · change (∑ v ∈ F.attach, t.val v.val • A.vertex v.val) =
        ∑ v ∈ F.attach, s.val v.val • A.vertex v.val
      rw [Finset.sum_attach F (fun v => t.val v • A.vertex v),
        Finset.sum_attach F (fun v => s.val v • A.vertex v)]
      exact hvec
  apply Subtype.ext
  funext v
  by_cases hv : v ∈ F
  · exact hu ⟨v,hv⟩
  · rw [ht v hv,hs v hv]

end Paper28
