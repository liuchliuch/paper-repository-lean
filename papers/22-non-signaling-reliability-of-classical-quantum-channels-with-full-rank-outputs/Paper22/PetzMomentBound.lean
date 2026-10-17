import Paper22.TestingPetzBound

/-! The Petz moment bound which evaluates the density optimization in the
finite-block MC achievability estimate. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22
variable {n d : ℕ}

theorem matrix_rpow_inverse_exponent {A : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) {α : ℝ} (hα : 0 < α) :
    CFC.rpow (CFC.rpow A (1/α)) α = A := by
  have he : CFC.rpow (CFC.rpow A (1/α)) α = CFC.rpow A ((1/α)*α) :=
    CFC.rpow_rpow_of_exponent_nonneg A (1/α) α (one_div_nonneg.mpr hα.le) hα.le hA
  rw [one_div_mul_cancel hα.ne'] at he
  exact he.trans (CFC.rpow_one A hA)

/-- The positive matrix Holder bound, derived by normalizing a matrix power
and applying the actual density-matrix Petz inequality. -/
theorem trace_mul_rpow_le_moment {A σ : Matrix (Fin d) (Fin d) ℂ}
    (hA : 0 ≤ A) (hσ : IsDensity σ) {α : ℝ} (hα : α ∈ Set.Ioo 0 1) :
    (A*CFC.rpow σ (1-α)).trace.re ≤ (CFC.rpow A (1/α)).trace.re ^ α := by
  let Y := CFC.rpow A (1/α)
  have hY : 0 ≤ Y := CFC.rpow_nonneg (a := A) (y := 1/α)
  have hYA : CFC.rpow Y α = A := matrix_rpow_inverse_exponent hA hα.1
  have ht0 : 0 ≤ Y.trace.re := hY.posSemidef.trace_nonneg.1
  rcases eq_or_lt_of_le ht0 with ht | ht
  · have hY0 := matrix_eq_zero_of_trace_re_eq_zero hY ht.symm
    have hA0 : A = 0 := by
      rw [hY0,CFC.zero_rpow hα.1.ne'] at hYA
      exact hYA.symm
    calc (A*CFC.rpow σ (1-α)).trace.re = 0 := by
           rw [hA0,Matrix.zero_mul,Matrix.trace_zero,Complex.zero_re]
         _ ≤ _ := Real.rpow_nonneg ht0 α
  · let τ := Y.trace.re⁻¹ • Y
    have hτ : IsDensity τ := normalize_positive_matrix hY ht
    have hYτ : Y=Y.trace.re • τ := by
      simp only [τ,smul_smul,mul_inv_cancel₀ ht.ne',one_smul]
    have hAτ : A = (Y.trace.re ^ α) • CFC.rpow τ α := by
      calc A = CFC.rpow Y α := hYA.symm
           _ = CFC.rpow (Y.trace.re • τ) α := congrArg (fun Z => CFC.rpow Z α) hYτ
           _ = _ := matrix_rpow_smul hτ.nonneg ht.le hα.1.le
    have htrace : (A*CFC.rpow σ (1-α)).trace.re = Y.trace.re ^ α * petzTrace α τ σ := by
      rw [hAτ,Matrix.smul_mul,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]
      rfl
    rw [htrace]
    exact mul_le_of_le_one_right (Real.rpow_nonneg ht.le _) (petzTrace_le_one hτ hσ hα)

/-- The averaged output powers used in the Sibson/Petz moment. -/
def petzPowerMixture (V : CQChannel n d) (q : Fin n → ℝ) (α : ℝ) :
    Matrix (Fin d) (Fin d) ℂ := ∑ x, q x • CFC.rpow (V.states x) α

theorem petzPowerMixture_nonneg (V : CQChannel n d) {q : Fin n → ℝ}
    (hq : ∀ x, 0 ≤ q x) (α : ℝ) : 0 ≤ petzPowerMixture V q α := by
  apply Finset.sum_nonneg
  intro x _
  have hp : 0 ≤ CFC.rpow (V.states x) α := CFC.rpow_nonneg
  exact (hp.posSemidef.smul (hq x)).nonneg

theorem sum_petzTrace_eq_mixture (V : CQChannel n d) (q : Fin n → ℝ) (α : ℝ)
    (σ : Matrix (Fin d) (Fin d) ℂ) :
    (∑ x, q x * petzTrace α (V.states x) σ) =
      (petzPowerMixture V q α*CFC.rpow σ (1-α)).trace.re := by
  simp only [petzPowerMixture,petzTrace,Matrix.sum_mul,Matrix.trace_sum,Complex.re_sum,
    Matrix.smul_mul,Matrix.trace_smul,Complex.smul_re,smul_eq_mul]

/-- A completely evaluated finite-block MC bound in terms of the actual
Petz power mixture; no optimization oracle is used. -/
theorem epsMC_le_petz_moment (V : CQChannel n d)
    {q : Fin n → ℝ} (hq0 : ∀ x, 0 ≤ q x) (hq1 : ∑ x, q x=1)
    {L α : ℝ} (hL : 0 < L) (hα : α ∈ Set.Ioo 0 1) :
    epsMC V L ≤
      (L ^ (1-α) * ((CFC.rpow (petzPowerMixture V q α) (1/α)).trace.re ^ α)) ^ (1/α) := by
  apply epsMC_le_petzTrace_bound V hq0 hq1 hL hα
    (Real.rpow_nonneg (CFC.rpow_nonneg (a := petzPowerMixture V q α) (y := 1/α)).posSemidef.trace_nonneg.1 _)
  intro σ hσ
  rw [sum_petzTrace_eq_mixture]
  exact trace_mul_rpow_le_moment (petzPowerMixture_nonneg V hq0 α) hσ hα

end Paper22
end
