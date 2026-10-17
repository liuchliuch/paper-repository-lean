import Paper22.HypothesisTesting

/-! Binary-testing lower bounds for the actual MC matrix program. -/
open scoped MatrixOrder ComplexOrder
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

/-- The positive-matrix dual expression, with multiplier already absorbing L. -/
def testingDualObjective (V : CQChannel n d) (L : ℝ) (q : Fin n → ℝ)
    (B : Matrix (Fin d) (Fin d) ℂ) : ℝ :=
  (∑ x, q x * testingRisk (V.states x) B) - (1/L) * B.trace.re

/-- A concrete feasible family bounds every positive-matrix testing dual value. -/
theorem testingDualObjective_le_programObjective (V : CQChannel n d)
    {L : ℝ} {q : Fin n → ℝ} {T : Fin n → Matrix (Fin d) (Fin d) ℂ}
    (h : MCFEasable L q T) {B : Matrix (Fin d) (Fin d) ℂ} (hB : 0 ≤ B) :
    testingDualObjective V L q B ≤ programObjective V.states q T := by
  have htest : (∑ x, q x * testingRisk (V.states x) B) ≤
      ∑ x, q x * testError (V.states x) B (T x) := by
    exact Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left
      (testingRisk_le_testError (V.isDensity x).posSemidef.nonneg hB (h.effects x)) (h.nonneg x)
  have hnorm := trace_mul_mono_re hB.posSemidef h.2.2.2
  have hsum : (B * ∑ x, q x • T x).trace.re =
      ∑ x, q x * (B * T x).trace.re := by
    simp only [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum, Matrix.mul_smul,
      Matrix.trace_smul, Complex.smul_re, smul_eq_mul]
  rw [hsum, Matrix.mul_smul, Matrix.mul_one, Matrix.trace_smul,
    Complex.smul_re, smul_eq_mul] at hnorm
  have hid : (∑ x, q x * testError (V.states x) B (T x)) =
      programObjective V.states q T + ∑ x, q x * (B * T x).trace.re := by
    simp only [testError, programObjective, mul_add, Finset.sum_add_distrib]
  unfold testingDualObjective
  linarith

/-- Uniform binary-testing risk lower bounds the actual MC optimum. -/
theorem le_epsMC_of_testingRisk (V : CQChannel n d) (hn : 0 < n)
    {L : ℝ} (hL : 0 ≤ L) {B : Matrix (Fin d) (Fin d) ℂ} (hB : 0 ≤ B)
    {a : ℝ} (ha : ∀ x, a ≤ testingRisk (V.states x) B) :
    a - (1/L) * B.trace.re ≤ epsMC V L := by
  apply le_csInf
  · obtain ⟨q,T,h⟩ := mc_feasible_nonempty hn hL
    exact ⟨programObjective V.states q T, q, T, h, rfl⟩
  · rintro e ⟨q,T,h,rfl⟩
    have hsum : a ≤ ∑ x, q x * testingRisk (V.states x) B := by
      calc a = ∑ x, q x * a := by rw [← Finset.sum_mul, h.sum_eq_one, one_mul]
           _ ≤ _ := Finset.sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ha x) (h.nonneg x)
    exact (sub_le_sub_right hsum _).trans (testingDualObjective_le_programObjective V h hB)

end Paper22
end
