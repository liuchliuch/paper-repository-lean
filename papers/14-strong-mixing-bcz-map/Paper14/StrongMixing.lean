import Paper14.Basic
import Mathlib.Analysis.Real.Pi.Bounds
/-!
# Theorem 1: strong mixing of the BCZ map

Paper anchors: Thmtheorem1, Ex3, Ex4, S4.p11–p12.
-/
open MeasureTheory Filter Topology Set Real
namespace Paper14

/-- Theorem 1 is `Theorem1Statement` from `Paper14.Basic`. -/
def Theorem1Claim : Prop := Theorem1Statement

/-- Equivalent `L²` correlation form (paper Ex4). -/
def Theorem1L2Claim : Prop := StrongMixingL2 B m

/-- Paper S4.p12: `n((1-α/n)^{-2} - 1) → 2α` (using `((1-x)²)⁻¹` for the inverse square). -/
def ScaleLimitStatement : Prop :=
  ∀ α : ℝ, 0 < α →
    Tendsto (fun n : ℕ => (n:ℝ) * (((1 - α / n) ^ (2 : ℝ))⁻¹ - 1)) atTop (𝓝 (2 * α))

/-- Paper S4.p12 uses `π²/3 > 3`. -/
lemma pi_sq_div_three_gt_three : (3:ℝ) < π ^ 2 / 3 := by
  have h3 : (3:ℝ) < π := Real.pi_gt_three
  have h4 : (9:ℝ) < π ^ 2 := by nlinarith [h3]
  have h3p : (3:ℝ) ≠ 0 := by norm_num
  have h5 : (3:ℝ) * 3 < π ^ 2 := by nlinarith
  field_simp [h3p]
  nlinarith

/-- Algebraic identity: `((1-x)²)⁻¹ - 1 = x(2-x)/(1-x)²` for `x ≠ 1`. -/
lemma one_sub_sq_inv_sub_one (x : ℝ) (hx : x ≠ 1) :
    ((1 - x) ^ (2 : ℝ))⁻¹ - 1 = x * (2 - x) / (1 - x) ^ 2 := by
  have h1 : (1 - x) ≠ 0 := by
    intro h
    apply hx
    linarith
  have h2 : (1 - x) ^ (2 : ℝ) = (1 - x) * (1 - x) := by
    rw [Real.rpow_two]; ring
  rw [h2]
  field_simp [h1]
  ring_nf

end Paper14
