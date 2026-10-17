import Paper28.ChartProjectionChoices
import Paper28.TranslatedCutoffs

/-! Actual conjugated finite-coordinate projections on every translated
chart. Their contractions, coordinate carriers and equivariance are derived
from the native regular isometries and chosen finite projections. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G J : Type*} [Group G] [DecidableEq G]

def translatedProjection (F : J → Finset G) (i : J×G) :
    CoordinateHilbert G →L[ℝ] CoordinateHilbert G :=
  (leftRegular i.2).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((l2CoordinateProjectionCLM (F i.1)).comp (leftRegular i.2⁻¹).toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem translatedProjection_apply (F : J → Finset G) (i : J×G) (u : CoordinateHilbert G) :
    translatedProjection F i u = leftRegular i.2 (l2CoordinateProjection (F i.1) (leftRegular i.2⁻¹ u)) := rfl

theorem leftRegular_mul_inv_apply (γ : G) (u : CoordinateHilbert G) :
    leftRegular γ (leftRegular γ⁻¹ u) = u := by
  rw [← leftRegular_mul,mul_inv_cancel,leftRegular_one]

theorem translatedProjection_norm_le (F : J → Finset G) (i : J×G) (u : CoordinateHilbert G) :
    ‖translatedProjection F i u‖ ≤ ‖u‖ := by
  rw [translatedProjection_apply,(leftRegular i.2).norm_map]
  exact (l2CoordinateProjection_norm_le _ _).trans_eq ((leftRegular i.2⁻¹).norm_map u)

theorem translatedProjection_error (F : J → Finset G) (i : J×G) (u : CoordinateHilbert G) :
    ‖translatedProjection F i u-u‖ =
      ‖l2CoordinateProjection (F i.1) (leftRegular i.2⁻¹ u)-leftRegular i.2⁻¹ u‖ := by
  calc
    _ = ‖leftRegular i.2 (l2CoordinateProjection (F i.1) (leftRegular i.2⁻¹ u)) -
        leftRegular i.2 (leftRegular i.2⁻¹ u)‖ := by rw [leftRegular_mul_inv_apply]; rfl
    _ = _ := by rw [← map_sub,(leftRegular i.2).norm_map]

theorem translatedProjection_mem (F : J → Finset G) (i : J×G) (u : CoordinateHilbert G) :
    translatedProjection F i u ∈ coordinateSupportSubspace ((F i.1).image (fun g => i.2*g)) :=
  leftRegular_mem_coordinateSupport _ _ _ (l2CoordinateProjection_mem _ _)

theorem translatedProjection_equivariant (F : J → Finset G) (j : J) (γ δ : G) (u : CoordinateHilbert G) :
    translatedProjection F (j,δ*γ) (leftRegular δ u) = leftRegular δ (translatedProjection F (j,γ) u) := by
  simp only [translatedProjection_apply]
  rw [← leftRegular_mul (δ*γ)⁻¹ δ]
  have he : (δ*γ)⁻¹*δ = γ⁻¹ := by group
  rw [he,leftRegular_mul]

end Paper28
