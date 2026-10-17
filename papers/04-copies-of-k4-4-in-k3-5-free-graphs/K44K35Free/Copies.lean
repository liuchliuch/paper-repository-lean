import K44K35Free.Construction
import K44K35Free.RandomPairing
import K44K35Free.GaussianPlanes
import K44K35Free.GeometrySections
import K44K35Free.Counts
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! The geometric edge multiplicity bound and the bridge from the constructed
plane pairs to the graph's unlabelled copy count. -/
noncomputable section
local instance copiesLocalInstance1 {A : Type*} : DecidableEq A := Classical.decEq A
namespace K44K35Free.Construction
open Geometry Finset Module
variable {F : Type*} [Field F] [Fintype F]

private theorem designatedPairs_random_eq (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) :
    designatedPairs α c T = RandomPairing.designatedPairs (richPlanes α c) polarEquiv T := by
  classical
  ext D
  have hd : D.1 = leftDual T D.2 ↔ mapPlane T D.2 = polar D.1 := by
    constructor
    · intro h
      rw [h, leftDual_apply, polar_polar]
    · intro h
      have hp := congrArg polar h
      simpa using hp.symm
  simp only [designatedPairs, RandomPairing.designatedPairs, mem_filter,
    mem_product, generalLinear_smul_plane]
  exact and_congr_right fun _ => hd

/-- The endpoint's orthogonal space is a genuine vector hyperplane. -/
theorem edgeHyperplane_finrank (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (r : Param F) :
    finrank F (edgeHyperplane α c T r) = 5 := by
  have hv : T (point α c r) ≠ 0 := by
    intro h
    exact point_ne_zero α c r (T.injective (by simpa using h))
  have hdual : dotForm (T (point α c r)) ≠ 0 := by
    intro h
    apply hv
    apply dotForm_nondegenerate
    intro w
    exact congrArg (fun l : Module.Dual F (V F) => l w) h
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero hdual
  change finrank F (edgeHyperplane α c T r) + 1 = finrank F (V F) at h
  have hdim : finrank F (V F) = 6 := by simp [V]
  rw [hdim] at h
  omega

/-- Exact count of the candidate planes for an actual incidence edge. -/
theorem edgePlanes_card (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (p r : Param F) (hpr : Incidence α c T p r) :
    (edgePlanes α c T p r).card = gaussianBinom2 (Fintype.card F) := by
  classical
  let H := edgeHyperplane α c T r
  let L := Submodule.span F ({point α c p} : Set (V F))
  have hL : finrank F L = 1 := finrank_span_singleton (point_ne_zero α c p)
  have hLH : L ≤ H := by
    apply Submodule.span_le.mpr
    intro v hv
    rcases Set.mem_singleton_iff.mp hv with rfl
    change dotProduct (T (point α c r)) (point α c p) = 0
    rw [dotProduct_comm]
    exact hpr
  have hc := card_projective_planes_through_point_in_hyperplane H L
    (edgeHyperplane_finrank α c T r) hL hLH
  have he : (edgePlanes α c T p r).card =
      Nat.card {P : Grassmann F (V F) 3 // L ≤ P.val ∧ P.val ≤ H} := by
    rw [Nat.card_eq_fintype_card]
    simp only [Fintype.card_subtype, Set.toFinset_setOf]
    congr 1
    ext E
    simp [edgePlanes, L, H, Submodule.span_singleton_le_iff_mem]
  rw [he, hc]
  simp [gaussianBinom2, Nat.card_eq_fintype_card]

/-- Lemma 7 for the actual initial incidence graph and designated copies. -/
theorem designatedPairs_through_edge_le (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (e : Param F × Param F)
    (he : e ∈ initialEdges α c T) :
    ((designatedPairs α c T).filter (fun D => e ∈ copyEdges α c D)).card ≤
      gaussianBinom2 (Fintype.card F) := by
  classical
  rw [designatedPairs_random_eq]
  have h := designated_through_edge_le_edgePlanes α c T (richPlanes α c) e.1 e.2
  simpa only [copyEdges, Finset.mem_product,
    edgePlanes_card α c T e.1 e.2 ((mem_initialEdges α c T e.1 e.2).mp he)] using h

/-- Rich plane sections determine their planes, using the actual cap property. -/
theorem rich_plane_eq_of_section_eq (α : F) (c : Quartic F)
    (hα : K44K35Free.IsNonsquare α) (A B : Plane F) (hA : Rich α c A)
    (hAB : planeSection α c A = planeSection α c B) : A = B := by
  classical
  obtain ⟨p,q,r,hp,hq,hr,hpq,hpr,hqr⟩ := Finset.two_lt_card_iff.mp
    (by rw [hA.2]; omega : 2 < (planeSection α c A).card)
  have he := plane_eq_of_three_points α c hα p q r hpq hpr hqr A
    ((mem_section _ _ _ _).mp hp) ((mem_section _ _ _ _).mp hq)
    ((mem_section _ _ _ _).mp hr)
  have hf := plane_eq_of_three_points α c hα p q r hpq hpr hqr B
    ((mem_section _ _ _ _).mp (hAB ▸ hp)) ((mem_section _ _ _ _).mp (hAB ▸ hq))
    ((mem_section _ _ _ _).mp (hAB ▸ hr))
  exact he.symm.trans hf

/-- The ordered vertex sides of a designated plane pair. -/
def copySides (α : F) (c : Quartic F) (D : Plane F × Plane F) :
    Finset (Param F ⊕ Param F) × Finset (Param F ⊕ Param F) := by
  classical
  exact ((planeSection α c D.1).image Sum.inl, (planeSection α c D.2).image Sum.inr)

theorem surviving_pair_isK44Pair (α : F) (c : Quartic F)
    (T : V F ≃ₗ[F] V F) (L : ℕ) (R : Choices α c)
    (D : Plane F × Plane F) (hD : D ∈ survivingPairs α c T L R) :
    IsK44Pair (finalGraph α c T L R) (copySides α c D).1 (copySides α c D).2 := by
  classical
  have hs := (Finset.mem_filter.mp hD).2
  have hd := (mem_designatedPairs α c T D).mp
    ((Finset.mem_filter.mp ((Finset.mem_filter.mp hD).1)).1)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [copySides, Finset.card_image_of_injective _ Sum.inl_injective] using hd.1.2
  · simpa only [copySides, Finset.card_image_of_injective _ Sum.inr_injective] using hd.2.1.2
  · apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨p,hp,hpv⟩ := Finset.mem_image.mp hv
    obtain ⟨r,hr,hrv⟩ := Finset.mem_image.mp hw
    exact Sum.inl_ne_inr (hpv.trans hrv.symm)
  · intro a b ha hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hb
    change (p,r) ∈ prune α c T L R
    exact hs (Finset.mem_product.mpr ⟨hp,hr⟩)

/-- Designated pairs give different ordered side pairs. -/
theorem copySides_injOn_designated (α : F) (c : Quartic F)
    (hα : K44K35Free.IsNonsquare α) (T : V F ≃ₗ[F] V F) :
    Set.InjOn (copySides α c) (designatedPairs α c T) := by
  classical
  intro D hD E hE h
  have hd := (mem_designatedPairs α c T D).mp hD
  apply Prod.ext
  · apply rich_plane_eq_of_section_eq α c hα D.1 E.1 hd.1
    exact Finset.image_injective Sum.inl_injective (congrArg Prod.fst h)
  · apply rich_plane_eq_of_section_eq α c hα D.2 E.2 hd.2.1
    exact Finset.image_injective Sum.inr_injective (congrArg Prod.snd h)

private theorem copySides_ne_swap (α : F) (c : Quartic F)
    (D E : Plane F × Plane F) (hD : Rich α c D.1) :
    copySides α c D ≠ (copySides α c E).swap := by
  classical
  intro h
  have hn : (planeSection α c D.1).Nonempty := by
    rw [← Finset.card_pos, hD.2]
    omega
  obtain ⟨p,hp⟩ := hn
  have hm : (Sum.inl p : Param F ⊕ Param F) ∈ (copySides α c D).1 :=
    Finset.mem_image.mpr ⟨p,hp,rfl⟩
  rw [h] at hm
  obtain ⟨r,hr,heq⟩ := Finset.mem_image.mp hm
  exact Sum.inr_ne_inl heq

/-- Each surviving designated pair yields the two distinct orientations of one
unlabelled copy. The counted copies are therefore actual copies in the final graph. -/
theorem survivingPairs_card_le_numK44 (α : F) (c : Quartic F)
    (hα : K44K35Free.IsNonsquare α) (T : V F ≃ₗ[F] V F)
    (L : ℕ) (R : Choices α c) :
    (survivingPairs α c T L R).card ≤ numK44 (finalGraph α c T L R) := by
  classical
  let S := survivingPairs α c T L R
  let f : (Plane F × Plane F) × Bool →
      Finset (Param F ⊕ Param F) × Finset (Param F ⊕ Param F) :=
    fun a => if a.2 then (copySides α c a.1).swap else copySides α c a.1
  have hsub : S ⊆ designatedPairs α c T :=
    fun D hD => (Finset.mem_filter.mp (Finset.mem_filter.mp hD).1).1
  have hm : ∀ a ∈ S ×ˢ (univ : Finset Bool), f a ∈ orientedK44 (finalGraph α c T L R) := by
    rintro ⟨D,b⟩ ha
    have hD := (Finset.mem_product.mp ha).1
    have hd := surviving_pair_isK44Pair α c T L R D hD
    apply mem_orientedK44.mpr
    cases b
    · exact hd
    · refine ⟨hd.2.1, hd.1, hd.2.2.1.symm, ?_⟩
      intro a b ha hb
      exact (hd.2.2.2 hb ha).symm
  have hi : Set.InjOn f (↑(S ×ˢ (univ : Finset Bool)) : Set _) := by
    rintro ⟨D,b⟩ hD ⟨E,d⟩ hE heq
    have hD' := hsub (Finset.mem_product.mp hD).1
    have hE' := hsub (Finset.mem_product.mp hE).1
    have hd := (mem_designatedPairs α c T D).mp hD'
    have he := (mem_designatedPairs α c T E).mp hE'
    cases b <;> cases d
    · have hDE := copySides_injOn_designated α c hα T hD' hE' heq
      exact Prod.ext hDE rfl
    · exact False.elim (copySides_ne_swap α c D E hd.1 heq)
    · exact False.elim (copySides_ne_swap α c E D he.1 heq.symm)
    · have hDE := copySides_injOn_designated α c hα T hD' hE'
        (congrArg Prod.swap heq)
      exact Prod.ext hDE rfl
  have hcard := Finset.card_le_card_of_injOn f hm hi
  simp only [Finset.card_product, Finset.card_univ, Fintype.card_bool] at hcard
  change S.card ≤ (orientedK44 (finalGraph α c T L R)).card / 2
  exact (Nat.le_div_iff_mul_le (by omega : 0 < 2)).mpr hcard

end K44K35Free.Construction
