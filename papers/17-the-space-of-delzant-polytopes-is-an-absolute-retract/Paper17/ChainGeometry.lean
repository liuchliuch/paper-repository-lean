import Paper17.FanPresentation
import Mathlib.Topology.Algebra.Module.Basic

/-! Rigidity and smoothness transfer for actual normal fans. -/
noncomputable section
open scoped Topology BigOperators Pointwise
namespace Paper17

/-- Inclusion between full-dimensional normal cones at carrier points forces
those points to coincide. -/
theorem eq_of_normalCone_interior_subset {n : ℕ} (P : Polytope n) {v w : V n}
    (hv : v ∈ P.carrier) (hw : w ∈ P.carrier)
    (hi : (interior (normalConeAt P v : Set (V n))).Nonempty)
    (hsub : (normalConeAt P v : Set (V n)) ⊆ normalConeAt P w) : v = w := by
  let f : V n →ₗ[ℝ] ℝ :=
    { toFun := fun u => dot u v - dot u w
      map_add' := fun u z => by simp only [dot_add_left]; ring
      map_smul' := fun t u => by simp only [dot_smul_left, RingHom.id_apply, smul_eq_mul]; ring }
  have hker : (normalConeAt P v : Set (V n)) ⊆ (LinearMap.ker f) := by
    intro u hu
    change dot u v - dot u w = 0
    exact sub_eq_zero.mpr (le_antisymm (hsub hu v hv) (hu w hw))
  have htop : (LinearMap.ker f) = ⊤ := (LinearMap.ker f).eq_top_of_nonempty_interior' (hi.mono (interior_mono hker))
  ext i
  have hzero : f (Pi.single i 1) = 0 := by
    change Pi.single i 1 ∈ (LinearMap.ker f)
    rw [htop]
    trivial
  have heq : v i - w i = 0 := by simpa [f, dot, Pi.single_apply] using hzero
  exact sub_eq_zero.mp heq

/-- Smoothness transfers through mutual refinement for normal fans.
The proof uses rigidity of full-dimensional normal cones; the analogous
statement for arbitrary finite cone covers is false. -/
theorem normalFan_isSmooth_of_equivalent {n : ℕ} {P Q : Polytope n}
    (h : Fan.Equivalent (NormalFan P) (NormalFan Q)) (hs : (NormalFan Q).IsSmooth) :
    (NormalFan P).IsSmooth := by
  classical
  intro K hK hdim
  obtain ⟨L, hL, hKL⟩ := h.1 K hK
  obtain ⟨K', hK', hLK⟩ := h.2 L hL
  obtain ⟨v, hv, hKv⟩ := Finset.mem_image.mp hK
  obtain ⟨w, hw, hK'w⟩ := Finset.mem_image.mp hK'
  have hsame : v = w := eq_of_normalCone_interior_subset P
    (subset_convexHull ℝ _ hv) (subset_convexHull ℝ _ hw)
    (hKv ▸ hdim) (by simpa only [hKv, hK'w] using hKL.trans hLK)
  have hKK' : K = K' := by rw [← hKv, ← hK'w, hsame]
  have hKL' : K = L := Cone.ext (Set.Subset.antisymm hKL (hKK' ▸ hLK))
  rw [hKL']
  exact hs L hL (hKL' ▸ hdim)

/-- Positive dilation preserves the entire finite normal-cone presentation. -/
theorem normalFan_smul_eq {n : ℕ} (P : Polytope n) {t : ℝ} (ht : 0 < t) :
    NormalFan (P.smul t) = NormalFan P := by
  classical
  have hc : (NormalFan (P.smul t)).cones = (NormalFan P).cones := by
    ext K
    constructor
    · rintro hK
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hK
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hy
      exact Finset.mem_image.mpr ⟨v, hv, Cone.ext
        (normalConeAt_smul ht (subset_convexHull ℝ _ hv)).symm⟩
    · rintro hK
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hK
      exact Finset.mem_image.mpr ⟨t • v, Finset.mem_image.mpr ⟨v, hv, rfl⟩,
        Cone.ext (normalConeAt_smul ht (subset_convexHull ℝ _ hv))⟩
  cases hP : NormalFan (P.smul t)
  cases hQ : NormalFan P
  simp_all only [Fan.mk.injEq]

namespace DelzantPolytope
/-- Positive two-term Minkowski interpolation along a refinement chain is Delzant. -/
theorem lemma_2_1_pair {n : ℕ} {P Q : DelzantPolytope n}
    (h : le P Q) {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    Fan.Equivalent (NormalFan ((P.val.smul α).add (Q.val.smul β))) (NormalFan Q.val) ∧
    IsDelzant ((P.val.smul α).add (Q.val.smul β)) := by
  have hadd := normalFan_add (P.val.smul α) (Q.val.smul β)
  rw [normalFan_smul_eq P.val hα, normalFan_smul_eq Q.val hβ] at hadd
  have hmeet := Fan.meet_equiv_of_refines h
  have heq : Fan.Equivalent (NormalFan ((P.val.smul α).add (Q.val.smul β)))
      (NormalFan Q.val) :=
    ⟨Fan.refines_trans hadd.1 hmeet.1, Fan.refines_trans hmeet.2 hadd.2⟩
  refine ⟨heq, ?_, normalFan_isSmooth_of_equivalent heq Q.property.2⟩
  let KP := PosBody.smul α hα.ne' (P.val.toPosBody P.property.1)
  let KQ := PosBody.smul β hβ.ne' (Q.val.toPosBody Q.property.1)
  change (interior (((P.val.smul α).add (Q.val.smul β)).carrier)).Nonempty
  rw [carrier_add_eq, carrier_smul_eq, carrier_smul_eq]
  exact (PosBody.add KP KQ).interior_nonempty
end DelzantPolytope

end Paper17
