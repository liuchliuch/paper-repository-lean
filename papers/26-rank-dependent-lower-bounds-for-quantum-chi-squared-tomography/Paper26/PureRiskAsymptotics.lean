import Paper26.A1MinimaxValue
import Mathlib.Analysis.SpecificLimits.Basic

/-! Appendix A's large-sample consequence of the proved exact minimax value.
The algebra and limits below use no additional external input. The quantitative
relative error also makes the regime n much larger than d² explicit. -/
noncomputable section
open Filter Topology

namespace Paper26.PureRiskAsymptotics

def risk (d : ℕ) (n : ℝ) : ℝ :=
  (Real.sqrt (n+1) + d - 1)^2 / (n+d) - 1

theorem risk_eq_appendixARisk (d : ℕ) (n : ℝ) :
    risk d n = PureMinimax.appendixARisk (ι := Fin d) n := by
  simp only [risk, PureMinimax.appendixARisk, Fintype.card_fin]

theorem risk_nonneg {d : ℕ} (hd : 1 ≤ d) {n : ℝ} (hn : 0 ≤ n) :
    0 ≤ risk d n := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht1 : 1 ≤ Real.sqrt (n+1) := Real.one_le_sqrt.mpr (by linarith)
  have ht2 : Real.sqrt (n+1)^2 = n+1 := Real.sq_sqrt (by linarith)
  have hk : 0 ≤ (d : ℝ)-1 := sub_nonneg.mpr hd'
  unfold risk
  apply sub_nonneg.mpr
  apply (le_div_iff₀ (by linarith : 0 < n+(d : ℝ))).mpr
  nlinarith [mul_nonneg hk (by linarith : 0 ≤ 2*Real.sqrt (n+1)+(d : ℝ)-2)]

theorem risk_factored {d : ℕ} (hd : 1 ≤ d) {n : ℝ} (hn : 0 ≤ n) :
    risk d n = ((d : ℝ)-1)*(2*Real.sqrt (n+1)+d-2)/(n+d) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : n+(d : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hs : Real.sqrt (n+1)^2 = n+1 := Real.sq_sqrt (by linarith)
  unfold risk
  apply (eq_div_iff hden).mpr
  rw [sub_mul, div_mul_cancel₀ _ hden, one_mul]
  nlinarith

theorem scaled_risk_inverse {d : ℕ} (hd : 1 ≤ d) {n : ℝ} (hn : 0 ≤ n) :
    Real.sqrt (n+1)*risk d n =
      ((d : ℝ)-1)*(2+((d : ℝ)-2)*(1/Real.sqrt (n+1))) /
        (1+((d : ℝ)-1)*(1/Real.sqrt (n+1))^2) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have ht : 0 < Real.sqrt (n+1) := Real.sqrt_pos.mpr (by linarith)
  have ht2 : Real.sqrt (n+1)^2 = n+1 := Real.sq_sqrt (by linarith)
  have hden : 0 < n+(d : ℝ) := by linarith
  have hk : 0 ≤ (d : ℝ)-1 := sub_nonneg.mpr hd'
  have hsmall : 0 < 1+((d : ℝ)-1)*(1/Real.sqrt (n+1))^2 := by positivity
  rw [risk_factored hd hn]
  apply (eq_div_iff hsmall.ne').mpr
  field_simp
  rw [ht2]
  ring

/-- A uniform relative-error bound. In particular d/sqrt(n+1) tending to
zero forces the source asymptotic, even when the dimension varies. -/
theorem relative_error_le {d : ℕ} (hd : 2 ≤ d) {n : ℝ} (hn : 0 ≤ n) :
    |Real.sqrt (n+1)*risk d n/(2*((d : ℝ)-1))-1| ≤
      2*(d : ℝ)/Real.sqrt (n+1) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hd2 : 0 ≤ (d : ℝ)-2 := sub_nonneg.mpr hd'
  have ht : 0 < Real.sqrt (n+1) := Real.sqrt_pos.mpr (by linarith)
  have ht1 : 1 ≤ Real.sqrt (n+1) := Real.one_le_sqrt.mpr (by linarith)
  have ht2 : Real.sqrt (n+1)^2 = n+1 := Real.sq_sqrt (by linarith)
  have hk : 0 < (d : ℝ)-1 := by linarith
  have hden : 0 < n+(d : ℝ) := by linarith
  have he : Real.sqrt (n+1)*risk d n/(2*((d : ℝ)-1))-1 =
      (((d : ℝ)-2)*Real.sqrt (n+1)/2-((d : ℝ)-1))/(n+d) := by
    rw [risk_factored (by omega) hn]
    field_simp
    nlinarith
  rw [he, abs_div, abs_of_pos hden]
  apply (div_le_div_iff₀ hden ht).mpr
  have habs : |((d : ℝ)-2)*Real.sqrt (n+1)/2-((d : ℝ)-1)| ≤
      ((d : ℝ)-2)*Real.sqrt (n+1)/2+((d : ℝ)-1) := by
    exact abs_sub _ _ |>.trans_eq (by
      rw [abs_of_nonneg (by positivity), abs_of_nonneg hk.le])
  have hdt : (d : ℝ)-1 ≤ ((d : ℝ)-1)*Real.sqrt (n+1) :=
    le_mul_of_one_le_right hk.le ht1
  have haux : ((d : ℝ)-2)*Real.sqrt (n+1)/2+((d : ℝ)-1) ≤
      2*(d : ℝ)*Real.sqrt (n+1) := by nlinarith
  have hmul := mul_le_mul_of_nonneg_right (habs.trans haux) ht.le
  nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ d) (by linarith : (0 : ℝ) ≤ d-1)]

theorem inverse_sqrt_tendsto_zero :
    Tendsto (fun n : ℕ => 1/Real.sqrt ((n : ℝ)+1)) atTop (𝓝 0) := by
  have h := Real.continuous_sqrt.continuousAt.tendsto.comp
    tendsto_one_div_add_atTop_nhds_zero_nat
  simpa only [Function.comp_def, Real.sqrt_zero, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1),
    Real.sqrt_one] using h

theorem sqrt_add_one_mul_risk_tendsto {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ)+1)*risk d n) atTop
      (𝓝 (2*((d : ℝ)-1))) := by
  have h : Tendsto (fun n : ℕ =>
      ((d : ℝ)-1)*(2+((d : ℝ)-2)*(1/Real.sqrt ((n : ℝ)+1))) /
        (1+((d : ℝ)-1)*(1/Real.sqrt ((n : ℝ)+1))^2)) atTop
      (𝓝 (((d : ℝ)-1)*(2+((d : ℝ)-2)*0)/(1+((d : ℝ)-1)*0^2))) :=
    (tendsto_const_nhds.mul
    (tendsto_const_nhds.add (tendsto_const_nhds.mul inverse_sqrt_tendsto_zero))).div
    (tendsto_const_nhds.add (tendsto_const_nhds.mul (inverse_sqrt_tendsto_zero.pow 2)))
    (by norm_num : (1 : ℝ)+((d : ℝ)-1)*0^2 ≠ 0)
  simp only [mul_zero, add_zero, zero_pow (by norm_num : 2 ≠ 0), div_one] at h
  convert h using 1
  · ext n
    exact scaled_risk_inverse hd (Nat.cast_nonneg n)
  · congr 1
    ring

/-- The exact source leading coefficient, including the zero coefficient
at d=1. Together with equation_50 this is an actual minimax-risk consequence. -/
theorem sqrt_mul_risk_tendsto {d : ℕ} (hd : 1 ≤ d) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ)*risk d n) atTop
      (𝓝 (2*((d : ℝ)-1))) := by
  have hr : Tendsto (fun n : ℕ => (n : ℝ)/((n : ℝ)+1)) atTop (𝓝 1) := by
    have h : Tendsto (fun n : ℕ => (1 : ℝ)-1/((n : ℝ)+1)) atTop (𝓝 (1-0)) :=
      tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    simp only [sub_zero] at h
    convert h using 1
    ext n
    field_simp
    ring
  have hs := Real.continuous_sqrt.continuousAt.tendsto.comp hr
  rw [Real.sqrt_one] at hs
  have h := hs.mul (sqrt_add_one_mul_risk_tendsto hd)
  simp only [one_mul] at h
  convert h using 1
  ext n
  simp only [Function.comp_def]
  rw [Real.sqrt_div (Nat.cast_nonneg n)]
  have ht : Real.sqrt ((n : ℝ)+1) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by positivity))
  field_simp

/-- The same limit stated directly for the actual operator minimax value.
All external parameters are exactly those of the proved equation_50. -/
theorem sqrt_mul_minimax_tendsto {d : ℕ} (hd : 1 ≤ d)
    (μ : MeasureTheory.Measure (HaarFrames.Frame (Fin d) (Fin 1)))
    [MeasureTheory.IsProbabilityMeasure μ]
    (H : PureCovariant.HaarTensorMomentInput μ)
    (P : ∀ n, SymmetricSupport.SymmetricProjectorInput (Fin d) n)
    (R : ∀ n, A1MinimaxValue.RNFamily (Fin d) n) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) *
      (A1MinimaxValue.minimaxRisk (R n)).toReal) atTop (𝓝 (2*((d : ℝ)-1))) := by
  letI : NeZero d := ⟨by omega⟩
  have he (n : ℕ) : (A1MinimaxValue.minimaxRisk (R n)).toReal = risk d n := by
    rw [A1MinimaxValue.equation_50 μ H (P n) (P (n+1)) (R n)]
    simpa only [Fintype.card_fin, risk] using
      ENNReal.toReal_ofReal (risk_nonneg hd (Nat.cast_nonneg n))
  simp only [he]
  exact sqrt_mul_risk_tendsto hd

end Paper26.PureRiskAsymptotics
