import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Paper08.Basic
import Paper08.Coeff
import Paper08.FPTAS

/-!
# Appendix A and B

* Lemma A.1 — primal degree at most one (midpoint-rule algebra).
* Proposition B.1 — deterministic value-query scale (fooling-function core).
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace Appendix

open Coeff FPTAS

/-! ## Appendix A: primal degree at most one -/

/-- Nonnegativity of the numerical product-Lipschitz majorant.
The actual product estimate is `SmallDegree.product_lipschitz`. -/
lemma product_lipschitz_majorant_nonneg (Δ : ℕ) (k U : ℝ) (hk : 0 < k) (hU : 1 < U)
    (hΔ : 1 ≤ Δ) :
    0 ≤ (2 * Δ : ℝ) * k * U ^ (2 * Δ - 1) := by
  positivity

/-- Nonnegativity of the numerical midpoint error majorant. -/
lemma midpoint_error_majorant_nonneg (T a : ℝ) (hT : 0 ≤ T) (ha : 0 ≤ a) :
    0 ≤ T * Real.sqrt 2 * a / 2 := by
  positivity

/-- Nonnegativity of the numerical product-sample error majorant.
The actual sample error estimate is `SmallDegree.product_perturbation`. -/
lemma sample_error_majorant_nonneg (Δ : ℕ) (U₀ b : ℝ) (hU₀ : 1 < U₀) (_hb : 0 ≤ b) :
    0 ≤ (2 * Δ : ℝ) * U₀ ^ (2 * Δ - 1) * 2 ^ (-b) := by
  positivity

/-- Logarithm is 1-Lipschitz on `[1,∞)`: `|log x - log y| ≤ |x - y|` when
`x,y ≥ 1`.  This is the last step of Lemma A.1. -/
lemma log_lipschitz_one {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    |Real.log x - Real.log y| ≤ |x - y| :=
  log_abs_sub_le_abs_sub hx hy

/-- The logarithm of a product of numbers at least one is nonnegative. -/
lemma component_log_sum {ι : Type*} [Fintype ι] (I : ι → ℝ) (hI : ∀ i, 1 ≤ I i) :
    0 ≤ Real.log (∏ i, I i) := by
  have hpos : 0 < ∏ i, I i := by
    apply Finset.prod_pos
    intro i _
    have := hI i
    linarith
  have hle : 1 ≤ ∏ i, I i := by
    apply Finset.prod_induction (f := I) (p := fun x => 1 ≤ x)
    · intro a b ha hb; nlinarith
    · norm_num
    · intro i _; exact hI i
  exact Real.log_nonneg hle

/-! ## Appendix B: deterministic value-query scale -/

/-- Bump function `p(t) = 16 t² (1-t)²` on `[0,1]`. -/
def bump (t : ℝ) : ℝ := 16 * t ^ 2 * (1 - t) ^ 2

lemma bump_nonneg (t : ℝ) : 0 ≤ bump t := by
  unfold bump
  positivity

lemma bump_le_one {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) : bump t ≤ 1 := by
  unfold bump
  have h4 : 4 * t * (1 - t) ≤ 1 := by
    have : 0 ≤ (2 * t - 1) ^ 2 := sq_nonneg _
    nlinarith
  have hform : 16 * t ^ 2 * (1 - t) ^ 2 = (4 * t * (1 - t)) ^ 2 := by ring
  rw [hform]
  have hnn : 0 ≤ 4 * t * (1 - t) := by
    have h1 : 0 ≤ t := ht.1
    have h2 : t ≤ 1 := ht.2
    nlinarith
  have habs : |4 * t * (1 - t)| ≤ 1 := abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have hsq : (4 * t * (1 - t)) ^ 2 ≤ 1 := by
    have h := abs_le.mp habs
    nlinarith
  exact hsq

/-- Nonnegativity of the numerical gradient majorant; this is not a
gradient estimate for the bump function. -/
lemma grad_phi_majorant_nonneg (r : ℕ) : 0 ≤ 8 * Real.sqrt r :=
  mul_nonneg (by norm_num) (Real.sqrt_nonneg _)

/-- Lower-bound constant `c₀ = a₀ J_r / 6` of Proposition B.1. -/
lemma c0_nonneg (a₀ J_r : ℝ) (ha₀ : 0 ≤ a₀) (hJ : 0 ≤ J_r) :
    0 ≤ a₀ * J_r / 6 := by
  positivity

/-- Jensen step of (B.1): `∑_e (N_e+1)^{-1/r} ≥ m^{1+1/r} (N_qry+m)^{-1/r}`.
We record the exponent arithmetic `1 + 1/r = (r+1)/r`. -/
lemma jensen_exp_form (r : ℕ) (hr : 1 ≤ r) :
    (1:ℝ) + 1 / r = (r + 1 : ℝ) / r := by
  field_simp

/-- Positivity of the mesh-size expression in the converse upper bound. -/
lemma surrogate_mesh_pos (ε K r M : ℝ) (hε : 0 < ε) (hK : 0 < K)
    (hr : 0 < r) (hM : 0 < M) :
    0 < ε / (2 * K * Real.sqrt r * M) := by
  positivity

end Appendix
end Paper08
