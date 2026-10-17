import Paper22.TestingStrongDuality
import Paper22.DivergencePetz

/-! Finite-block MC achievability from the actual Petz trace. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

/-- Scalar homogeneity of matrix powers, also for singular matrices. -/
theorem matrix_rpow_smul {A : Matrix (Fin d) (Fin d) ℂ} (hA : 0 ≤ A)
    {t α : ℝ} (ht : 0 ≤ t) (hα : 0 ≤ α) :
    CFC.rpow (t • A) α = (t ^ α) • CFC.rpow A α := by
  let r : NNReal := ⟨t,ht⟩
  have hf : Continuous (fun x : NNReal => x ^ α) := NNReal.continuous_rpow_const hα
  change cfc (fun x : NNReal => x ^ α) (r • A) = _
  rw [← cfc_comp_const_mul r (fun x : NNReal => x ^ α) A
    (hf := by exact hf.continuousOn) (ha := hA)]
  simp_rw [NNReal.mul_rpow]
  rw [cfc_const_mul (r ^ α) (fun x : NNReal => x ^ α) A (hf := by exact hf.continuousOn)]
  change (((r ^ α : NNReal) : ℝ)) • CFC.rpow A α = _
  simp only [NNReal.coe_rpow, r]
  rfl

theorem petzTrace_smul_right {A B : Matrix (Fin d) (Fin d) ℂ}
    (hB : 0 ≤ B) {t α : ℝ} (ht : 0 ≤ t) (hα : α ≤ 1) :
    petzTrace α A (t • B) = (t ^ (1-α)) * petzTrace α A B := by
  unfold petzTrace
  rw [matrix_rpow_smul hB ht (sub_nonneg.mpr hα), Matrix.mul_smul,
    Matrix.trace_smul, Complex.smul_re, smul_eq_mul]

theorem matrix_trace_eq_coe_re_of_nonneg {B : Matrix (Fin d) (Fin d) ℂ} (hB : 0 ≤ B) :
    B.trace = (B.trace.re : ℂ) := by
  apply Complex.ext
  · rfl
  · exact hB.posSemidef.trace_nonneg.2.symm

theorem matrix_eq_zero_of_trace_re_eq_zero {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : 0 ≤ B) (ht : B.trace.re = 0) : B = 0 := by
  apply hB.posSemidef.trace_eq_zero_iff.mp
  rw [matrix_trace_eq_coe_re_of_nonneg hB, ht, Complex.ofReal_zero]

theorem normalize_positive_matrix {B : Matrix (Fin d) (Fin d) ℂ}
    (hB : 0 ≤ B) (ht : 0 < B.trace.re) : IsDensity (B.trace.re⁻¹ • B) := by
  constructor
  · exact hB.posSemidef.smul (inv_nonneg.mpr ht.le)
  · rw [Matrix.trace_smul, matrix_trace_eq_coe_re_of_nonneg hB]
    simp only [Algebra.smul_def, Complex.coe_algebraMap, Complex.ofReal_re, ← Complex.ofReal_mul,
      inv_mul_cancel₀ ht.ne', Complex.ofReal_one]

/-- Scalar Young bound used after normalizing a PSD multiplier by its trace. -/
theorem young_testing_bound {α c s : ℝ} (hα : α ∈ Set.Ioo 0 1)
    (hc : 0 ≤ c) (hs : 0 ≤ s) : s ^ (1-α) * c - s ≤ c ^ (1/α) := by
  let u := c ^ (1/α)
  have hu : 0 ≤ u := Real.rpow_nonneg hc _
  have huc : u ^ α = c := by
    dsimp only [u]
    rw [← Real.rpow_mul hc, one_div_mul_cancel hα.1.ne', Real.rpow_one]
  have h := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := α) (w₂ := 1-α) (p₁ := u) (p₂ := s)
    hα.1.le (by linarith [hα.2]) hu hs (by ring)
  rw [huc] at h
  have hαu : α*u ≤ u := mul_le_of_le_one_left hu hα.2.le
  change _ ≤ u
  nlinarith [mul_nonneg hα.1.le hs]

/-- A distribution with uniformly small Petz average yields an actual MC code.
The right side is the non-asymptotic quantity later evaluated on tensor powers. -/
theorem epsMC_le_petzTrace_bound (V : CQChannel n d)
    {q : Fin n → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x = 1)
    {L α c : ℝ} (hL : 0 < L) (hα : α ∈ Set.Ioo 0 1) (hc : 0 ≤ c)
    (htrace : ∀ σ : Matrix (Fin d) (Fin d) ℂ, IsDensity σ →
      ∑ x, q x * petzTrace α (V.states x) σ ≤ c) :
    epsMC V L ≤ (L ^ (1-α) * c) ^ (1/α) := by
  apply epsMC_le_of_testingDual V hq0 hq1 hL.le
  intro B hB
  have ht0 : 0 ≤ B.trace.re := hB.posSemidef.trace_nonneg.1
  rcases eq_or_lt_of_le ht0 with ht | ht
  · have hBzero : B = 0 := matrix_eq_zero_of_trace_re_eq_zero hB ht.symm
    subst B
    unfold testingDualObjective
    have hzero (x : Fin n) : testingRisk (V.states x) 0 = 0 := by
      apply le_antisymm
      · have h := testingRisk_le_testError (V.isDensity x).nonneg (by rfl : (0:Matrix (Fin d) (Fin d) ℂ) ≤ 0) IsEffect.one
        simpa [testError] using h
      · exact testingRisk_nonneg (V.isDensity x).nonneg le_rfl
    simp only [hzero, mul_zero, Finset.sum_const_zero, Matrix.trace_zero, Complex.zero_re,
      sub_zero]
    positivity
  · let σ := B.trace.re⁻¹ • B
    have hσ : IsDensity σ := normalize_positive_matrix hB ht
    have hBσ : B = B.trace.re • σ := by
      simp only [σ, smul_smul, mul_inv_cancel₀ ht.ne', one_smul]
    have hsum : (∑ x, q x * testingRisk (V.states x) B) ≤
        B.trace.re ^ (1-α) * c := by
      calc _ ≤ ∑ x, q x * petzTrace α (V.states x) B := Finset.sum_le_sum fun x _ =>
             mul_le_mul_of_nonneg_left (testingRisk_le_petzTrace (V.isDensity x).nonneg hB hα) (hq0 x)
           _ = B.trace.re ^ (1-α) * ∑ x, q x * petzTrace α (V.states x) σ := by
             conv_lhs => arg 2; ext x; rw [hBσ,petzTrace_smul_right hσ.nonneg ht.le hα.2.le]
             rw [Finset.mul_sum]
             apply Finset.sum_congr rfl
             intro x _
             ring
           _ ≤ _ := mul_le_mul_of_nonneg_left (htrace σ hσ) (Real.rpow_nonneg ht.le _)
    let s := B.trace.re / L
    have hs : 0 ≤ s := div_nonneg ht.le hL.le
    have hts : B.trace.re = L*s := by dsimp [s]; field_simp
    have hy := young_testing_bound (c := L ^ (1-α)*c) hα
      (mul_nonneg (Real.rpow_nonneg hL.le _) hc) hs
    have heq : B.trace.re ^ (1-α)*c - (1/L)*B.trace.re =
        s ^ (1-α) * (L ^ (1-α)*c) - s := by
      rw [hts,Real.mul_rpow hL.le hs]
      field_simp <;> ring
    unfold testingDualObjective
    calc _ ≤ B.trace.re ^ (1-α)*c - (1/L)*B.trace.re := sub_le_sub_right hsum _
         _ = s ^ (1-α) * (L ^ (1-α)*c) - s := heq
         _ ≤ _ := hy

end Paper22
end
