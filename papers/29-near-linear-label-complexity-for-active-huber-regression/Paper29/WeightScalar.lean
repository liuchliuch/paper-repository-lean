import Paper29.Geometry
import Paper29.ProcessTools
import Mathlib.Analysis.SpecialFunctions.Log.Basic

noncomputable section
open scoped BigOperators Classical
namespace Paper29.WeightConstruction

/-- Logarithm of the scalar factor in the exact Huber leverage update. -/
def logFactor (x : ℝ) : ℝ := Real.log (huber (Real.sqrt x)) - Real.log x

private theorem huber_sqrt_pos {x : ℝ} (hx : 0 < x) : 0 < huber (Real.sqrt x) := by
  apply lt_of_le_of_ne (huber_nonneg _)
  intro h
  have hz := (huber_eq_zero_iff _).mp h.symm
  exact (ne_of_gt (Real.sqrt_pos.2 hx)) hz

/-- Huber-specific scalar log contraction, derived from the proved lower-one,
upper-two scaling rather than assumed as a weight-scheme conclusion. -/
theorem logFactor_lipschitz {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |logFactor x - logFactor y| ≤ (1/2) * |Real.log x - Real.log y| := by
  suffices h : ∀ {x y : ℝ}, 0 < x → 0 < y → x ≤ y →
      |logFactor x - logFactor y| ≤ (1/2) * |Real.log x - Real.log y| by
    rcases le_total x y with hxy | hyx
    · exact h hx hy hxy
    · simpa only [abs_sub_comm] using h hy hx hyx
  intro x y hx hy hxy
  have hsx := Real.sqrt_pos.2 hx
  have hsy := Real.sqrt_pos.2 hy
  let l := Real.sqrt y / Real.sqrt x
  have hl : 1 ≤ l := (le_div_iff₀ hsx).2 (by simpa using Real.sqrt_le_sqrt hxy)
  have hl0 : 0 < l := div_pos hsy hsx
  have he : l * Real.sqrt x = Real.sqrt y := by dsimp [l]; field_simp
  have hscale := huber_scaling (t := Real.sqrt x) hl
  rw [he] at hscale
  have hhx := huber_sqrt_pos hx
  have hhy := huber_sqrt_pos hy
  have hlo := Real.log_le_log (mul_pos hl0 hhx) hscale.1
  have hhi := Real.log_le_log hhy hscale.2
  rw [Real.log_mul (ne_of_gt hl0) (ne_of_gt hhx)] at hlo
  rw [Real.log_mul (ne_of_gt (sq_pos_of_pos hl0)) (ne_of_gt hhx), Real.log_pow] at hhi
  have hlogl : Real.log l = (Real.log y - Real.log x) / 2 := by
    dsimp [l]
    rw [Real.log_div (ne_of_gt hsy) (ne_of_gt hsx), Real.log_sqrt hy.le,
      Real.log_sqrt hx.le]
    ring
  have hlogxy := Real.log_le_log hx hxy
  rw [hlogl] at hlo hhi
  unfold logFactor
  rw [abs_of_nonpos (sub_nonpos.mpr hlogxy)]
  apply abs_le.mpr
  constructor <;> norm_num at hhi ⊢ <;> linarith

end Paper29.WeightConstruction
