import Paper26.SampleLowerBounds

/-! The numerical substitution of the prior, successful-volume and Fisher
budgets into the posterior bound, Equations (30)--(33). Inputs are the
preceding component bounds; no final sample or success-rate conclusion is
an external field. The experiment-to-posterior connection is separate. -/
noncomputable section

namespace Paper26.InformationRateBounds

def rateConstant (K C₀ : ℝ) : ℝ := K * (C₀ + 8)

theorem rateConstant_pos {K C₀ : ℝ} (hK : 0 < K) (hC₀ : 0 ≤ C₀) :
    0 < rateConstant K C₀ := by unfold rateConstant; positivity

/-- One substitution handles both measurement budgets: `b=1` is collective,
and `b=r` is the adaptive one-copy budget (with its harmless factor-2 slack). -/
theorem success_rate {K C₀ r s b n scale vroot priorI dataI S : ℝ}
    (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hr : 0 < r) (hs : 0 < s) (hb : 0 < b)
    (hn : 0 ≤ n) (hscale : 0 ≤ scale) (hprior0 : 0 ≤ priorI) (hdata0 : 0 ≤ dataI)
    (hv : vroot ≤ K * scale / s)
    (hprior : priorI ≤ C₀ * r * s ^ 2)
    (hdata : dataI ≤ 8 * n * s / b)
    (hposterior : S ≤ vroot / (2 * r * s) * (priorI + dataI)) :
    S ≤ rateConstant K C₀ * scale * (1 + n / (r * s * b)) := by
  have hbudget : priorI + dataI ≤ C₀ * r * s ^ 2 + 8 * n * s / b := by linarith
  have hvroot := div_le_div_of_nonneg_right hv (by positivity : 0 ≤ 2 * r * s)
  have hnonneg : 0 ≤ K * scale / s / (2 * r * s) := by positivity
  calc
    S ≤ vroot / (2 * r * s) * (priorI + dataI) := hposterior
    _ ≤ (K * scale / s / (2 * r * s)) *
        (C₀ * r * s ^ 2 + 8 * n * s / b) :=
      mul_le_mul hvroot hbudget (add_nonneg hprior0 hdata0) hnonneg
    _ = K * scale * (C₀ / 2 + 4 * (n / (r * s * b))) := by field_simp; ring
    _ ≤ rateConstant K C₀ * scale * (1 + n / (r * s * b)) := by
      have ht : 0 ≤ n / (r * s * b) := by positivity
      have hscalar : C₀ / 2 + 4 * (n / (r * s * b)) ≤
          (C₀ + 8) * (1 + n / (r * s * b)) := by nlinarith
      have h := mul_le_mul_of_nonneg_left hscalar (mul_nonneg hK hscale)
      simpa only [rateConstant, mul_assoc, mul_left_comm, mul_comm] using h

/-- Equation (30) from the actual preceding numerical bounds. -/
theorem bures_collective_success {K C₀ r s n ε vroot priorI dataI S : ℝ}
    (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hr : 0 < r) (hs : 0 < s)
    (hn : 0 ≤ n) (hε : 0 ≤ ε) (hprior0 : 0 ≤ priorI) (hdata0 : 0 ≤ dataI)
    (hv : vroot ≤ K * (ε * Real.sqrt (r / s)) / s)
    (hprior : priorI ≤ C₀ * r * s ^ 2) (hdata : dataI ≤ 8 * n * s)
    (hposterior : S ≤ vroot / (2 * r * s) * (priorI + dataI)) :
    S ≤ rateConstant K C₀ * ε * Real.sqrt (r / s) * (1 + n / (r * s)) := by
  simpa only [mul_one, div_one, mul_assoc] using success_rate hK hC₀ hr hs
    (by norm_num : (0 : ℝ) < 1) hn (mul_nonneg hε (Real.sqrt_nonneg _))
    hprior0 hdata0 hv hprior (by simpa using hdata) hposterior

/-- Equation (31), preserving the source's stronger `4ns/r` budget. -/
theorem bures_one_copy_success {K C₀ r s n ε vroot priorI dataI S : ℝ}
    (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hr : 0 < r) (hs : 0 < s)
    (hn : 0 ≤ n) (hε : 0 ≤ ε) (hprior0 : 0 ≤ priorI) (hdata0 : 0 ≤ dataI)
    (hv : vroot ≤ K * (ε * Real.sqrt (r / s)) / s)
    (hprior : priorI ≤ C₀ * r * s ^ 2) (hdata : dataI ≤ 4 * n * s / r)
    (hposterior : S ≤ vroot / (2 * r * s) * (priorI + dataI)) :
    S ≤ rateConstant K C₀ * ε * Real.sqrt (r / s) * (1 + n / (r ^ 2 * s)) := by
  have hd : dataI ≤ 8 * n * s / r := by
    apply hdata.trans
    apply div_le_div_of_nonneg_right _ hr.le
    nlinarith
  have h := success_rate hK hC₀ hr hs hr hn (mul_nonneg hε (Real.sqrt_nonneg _))
    hprior0 hdata0 hv hprior hd hposterior
  convert h using 1 <;> ring

/-- Equation (32). -/
theorem right_collective_success {K C₀ r s n ε vroot priorI dataI S : ℝ}
    (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hr : 0 < r) (hs : 0 < s)
    (hn : 0 ≤ n) (hprior0 : 0 ≤ priorI) (hdata0 : 0 ≤ dataI)
    (hv : vroot ≤ K * (r * ε ^ 2 / s) / s)
    (hprior : priorI ≤ C₀ * r * s ^ 2) (hdata : dataI ≤ 8 * n * s)
    (hposterior : S ≤ vroot / (2 * r * s) * (priorI + dataI)) :
    S ≤ rateConstant K C₀ * (r * ε ^ 2 / s) * (1 + n / (r * s)) := by
  simpa only [mul_one, div_one] using success_rate hK hC₀ hr hs
    (by norm_num : (0 : ℝ) < 1) hn (by positivity : 0 ≤ r * ε ^ 2 / s)
    hprior0 hdata0 hv hprior (by simpa using hdata) hposterior

/-- Equation (33). -/
theorem right_one_copy_success {K C₀ r s n ε vroot priorI dataI S : ℝ}
    (hK : 0 ≤ K) (hC₀ : 0 ≤ C₀) (hr : 0 < r) (hs : 0 < s)
    (hn : 0 ≤ n) (hprior0 : 0 ≤ priorI) (hdata0 : 0 ≤ dataI)
    (hv : vroot ≤ K * (r * ε ^ 2 / s) / s)
    (hprior : priorI ≤ C₀ * r * s ^ 2) (hdata : dataI ≤ 4 * n * s / r)
    (hposterior : S ≤ vroot / (2 * r * s) * (priorI + dataI)) :
    S ≤ rateConstant K C₀ * (r * ε ^ 2 / s) * (1 + n / (r ^ 2 * s)) := by
  have hd : dataI ≤ 8 * n * s / r := by
    apply hdata.trans
    apply div_le_div_of_nonneg_right _ hr.le
    nlinarith
  have h := success_rate hK hC₀ hr hs hr hn (by positivity : 0 ≤ r * ε ^ 2 / s)
    hprior0 hdata0 hv hprior hd hposterior
  convert h using 1 <;> ring

end Paper26.InformationRateBounds
