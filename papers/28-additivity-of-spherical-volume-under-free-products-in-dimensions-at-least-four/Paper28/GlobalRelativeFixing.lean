import Paper28.GlobalProjectionHomotopy
import Paper28.ProjectionErrorNeighborhood

/-! Exact relative fixing for the global construction. The input relative
pieces are the actual compact finite-support lifts of the prescribed finite
polyhedral presentation; no relative deformation map is an assumption. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G J A : Type*} [Group G] [DecidableEq G] [Fintype J]

/-- All group translates of the prescribed finite-support lifted pieces. -/
def liftedRelativePieces (P : A → Set (CoordinateHilbert G)) : Set (CoordinateHilbert G) :=
  {u | ∃ a : A, ∃ γ : G, ∃ v ∈ P a, leftRegular γ v = u}

theorem translatedProjection_fixed_relative (c : J → RegularSphere G)
    [∀ j, Fintype (regularStabilizer (c j).val)] (b : ∀ j, ContDiffBump (c j).val)
    (hR : ∀ j, (b j).rOut ≤ (1/8 : ℝ)) (F : J → Finset G)
    (P : A → Set (CoordinateHilbert G))
    (hFix : ∀ j, ∀ a, ∀ v ∈ P a, ∀ γ : G,
      dist (c j).val (leftRegular γ v) < (1/8 : ℝ) →
        l2CoordinateProjection (F j) (leftRegular γ v) = leftRegular γ v)
    (u : CoordinateHilbert G) (hu : u ∈ liftedRelativePieces P) (i : J×G)
    (hβ : translatedCutoff (fun j => (c j).val) b i u ≠ 0) : translatedProjection F i u = u := by
  obtain ⟨a,τ,v,hv,rfl⟩ := hu
  have hclose := translatedCutoff_support (fun j => (c j).val) b i (leftRegular τ v) hβ
  have hpre : dist (c i.1).val (leftRegular (i.2⁻¹*τ) v) < (1/8 : ℝ) := by
    rw [leftRegular_mul,dist_comm,leftRegular_inv_dist]
    exact hclose.trans_le (hR i.1)
  have he := hFix i.1 a v hv (i.2⁻¹*τ) hpre
  rw [translatedProjection_apply,← leftRegular_mul i.2⁻¹ τ,he,← leftRegular_mul]
  have hword : i.2*(i.2⁻¹*τ) = τ := by group
  rw [hword]

/-- Both the normalized map and its entire straight homotopy fix all lifts
of the prescribed relative set exactly. -/
theorem globalProjection_relative_fixed (c : J → RegularSphere G)
    [∀ j, Fintype (regularStabilizer (c j).val)] (b : ∀ j, ContDiffBump (c j).val)
    (hR : ∀ j, (b j).rOut ≤ (1/8 : ℝ)) (F : J → Finset G)
    (P : A → Set (CoordinateHilbert G))
    (hFix : ∀ j, ∀ a, ∀ v ∈ P a, ∀ γ : G,
      dist (c j).val (leftRegular γ v) < (1/8 : ℝ) →
        l2CoordinateProjection (F j) (leftRegular γ v) = leftRegular γ v)
    (u : CoordinateHilbert G) (hu : ‖u‖ = 1) (hRelative : u ∈ liftedRelativePieces P)
    (hD : 0 < cutoffDenominator (fun j => (c j).val) b u) :
    globalNormalizedProjection (fun j => (c j).val) b F u = u ∧
      ∀ t : ℝ, globalProjectionHomotopy (fun j => (c j).val) b F t u = u := by
  have hR' : ∀ j, (b j).rOut < (1/4 : ℝ) := fun j => lt_of_le_of_lt (hR j) (by norm_num)
  have he := globalProjection_fixed (fun j => (c j).val) b F hR' (fun j => (c j).property) u hu hD
    (fun i hi => translatedProjection_fixed_relative c b hR F P hFix u hRelative i hi)
  constructor
  · unfold globalNormalizedProjection
    rw [he,sphericalNormalize_fixed u hu]
  · exact globalProjectionHomotopy_fixed (fun j => (c j).val) b F u hu he

end Paper28
