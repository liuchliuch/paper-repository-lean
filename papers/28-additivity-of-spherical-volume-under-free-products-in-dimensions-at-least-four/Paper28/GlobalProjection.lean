import Paper28.TranslatedProjections
import Paper28.RelativeEquivariance

/-! The actual global equivariant weighted projection, defined by locally
finite translated sums, and its actual normalized map and straight homotopy. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open WithLp
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j)) (F : J → Finset G)

def globalProjection (u : CoordinateHilbert G) : CoordinateHilbert G :=
  ∑' i : J×G, normalizedCutoff c b i u • translatedProjection F i u

def globalNormalizedProjection (u : CoordinateHilbert G) : CoordinateHilbert G :=
  sphericalNormalize (globalProjection c b F u)

def globalProjectionHomotopy (t : ℝ) (u : CoordinateHilbert G) : CoordinateHilbert G :=
  sphericalNormalize ((1-t) • u + t • globalProjection c b F u)

theorem globalProjection_eq_sum (s : Finset (J×G)) (u : CoordinateHilbert G)
    (hzero : ∀ i ∉ s, translatedCutoff c b i u = 0) :
    globalProjection c b F u = ∑ i ∈ s, normalizedCutoff c b i u • translatedProjection F i u := by
  apply (hasSum_sum_of_ne_finset_zero (fun i hi => ?_)).tsum_eq
  simp only [normalizedCutoff,hzero i hi,zero_div,zero_smul]

/-- The infinite translated sum is exactly equivariant, not merely
well-defined after choosing coset representatives. -/
theorem globalProjection_equivariant (δ : G) (u : CoordinateHilbert G) :
    globalProjection c b F (leftRegular δ u) = leftRegular δ (globalProjection c b F u) := by
  let e : J×G ≃ J×G := Equiv.prodCongr (Equiv.refl J) (Equiv.mulLeft δ)
  unfold globalProjection
  calc
    _ = ∑' i : J×G, normalizedCutoff c b (e i) (leftRegular δ u) •
        translatedProjection F (e i) (leftRegular δ u) :=
      (e.tsum_eq (fun i => normalizedCutoff c b i (leftRegular δ u) • translatedProjection F i (leftRegular δ u))).symm
    _ = ∑' i : J×G, leftRegular δ (normalizedCutoff c b i u • translatedProjection F i u) := by
      apply tsum_congr
      intro i
      change normalizedCutoff c b (i.1,δ*i.2) (leftRegular δ u) •
        translatedProjection F (i.1,δ*i.2) (leftRegular δ u) = _
      rw [normalizedCutoff_equivariant,translatedProjection_equivariant,map_smul]
    _ = _ := ((leftRegular δ).toContinuousLinearEquiv.map_tsum
      (f := fun i : J×G => normalizedCutoff c b i u • translatedProjection F i u)).symm

theorem globalNormalizedProjection_equivariant (δ : G) (u : CoordinateHilbert G) :
    globalNormalizedProjection c b F (leftRegular δ u) = leftRegular δ (globalNormalizedProjection c b F u) := by
  unfold globalNormalizedProjection
  rw [globalProjection_equivariant,sphericalNormalize_map]

theorem globalProjectionHomotopy_equivariant (δ : G) (t : ℝ) (u : CoordinateHilbert G) :
    globalProjectionHomotopy c b F t (leftRegular δ u) = leftRegular δ (globalProjectionHomotopy c b F t u) := by
  unfold globalProjectionHomotopy
  rw [globalProjection_equivariant,← map_smul,← map_smul,← map_add,sphericalNormalize_map]

/-- In a lifted neighborhood the constructed normalized map has actual
finite coordinate support, given by the union of the active translated sets. -/
theorem globalNormalizedProjection_local_support (hR : ∀ j, (b j).rOut < (1/4 : ℝ))
    (hU : ∀ j, ‖c j‖ = 1) (u : CoordinateHilbert G) (hu : ‖u‖ = 1) :
    ∃ E : Finset G, ∀ v, dist u v < (1/2 : ℝ) →
      globalNormalizedProjection c b F v ∈ coordinateSupportSubspace E := by
  classical
  obtain ⟨s,hs⟩ := translatedCutoff_local_finite c b hR hU u hu
  let E := s.biUnion (fun i => (F i.1).image (fun g => i.2*g))
  refine ⟨E,?_⟩
  intro v hv
  unfold globalNormalizedProjection sphericalNormalize
  apply (coordinateSupportSubspace E).smul_mem
  rw [globalProjection_eq_sum c b F s v (fun i hi => hs v hv i hi)]
  apply Submodule.sum_mem
  intro i hi
  apply (coordinateSupportSubspace E).smul_mem
  exact coordinateSupportSubspace_mono _ E (Finset.subset_biUnion_of_mem _ hi)
    (translatedProjection_mem F i v)

end Paper28
