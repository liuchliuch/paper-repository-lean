import Paper09.Spectral
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

open Real Filter MeasureTheory
open scoped Topology

noncomputable section

namespace Paper09

/-- The truncated double-logarithmic statistic in (1.6). -/
def griffithsStatistic (n Y : ℝ) : ℝ :=
  log (log (max (exp 1) Y)) / log (log n)

/-- The explicit lower endpoint obtained by taking both logarithms in (1.5). -/
def lowerLoglogEndpoint (c a n : ℝ) : ℝ :=
  a + (log c - a * log (log (log n))) / log (log n)

/-- The explicit upper endpoint obtained by taking both logarithms in (1.5). -/
def upperLoglogEndpoint (C a b n : ℝ) : ℝ :=
  a + (log C + b * log (log (log n))) / log (log n)

theorem tendsto_loglog_atTop :
    Tendsto (fun n : ℝ => log (log n)) atTop atTop :=
  tendsto_log_atTop.comp tendsto_log_atTop

theorem tendsto_logloglog_div_loglog :
    Tendsto (fun n : ℝ => log (log (log n)) / log (log n)) atTop (𝓝 0) :=
  Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp tendsto_loglog_atTop

theorem tendsto_lowerLoglogEndpoint (c a : ℝ) :
    Tendsto (lowerLoglogEndpoint c a) atTop (𝓝 a) := by
  have hconst : Tendsto (fun n : ℝ => log c / log (log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_loglog_atTop
  have hsmall := hconst.sub ((tendsto_const_nhds (x := a)).mul tendsto_logloglog_div_loglog)
  have h := (tendsto_const_nhds (x := a)).add hsmall
  convert h using 1
  · ext n
    dsimp [lowerLoglogEndpoint]
    ring
  · simp

theorem tendsto_upperLoglogEndpoint (C a b : ℝ) :
    Tendsto (upperLoglogEndpoint C a b) atTop (𝓝 a) := by
  have hconst : Tendsto (fun n : ℝ => log C / log (log n)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_loglog_atTop
  have hsmall := hconst.add ((tendsto_const_nhds (x := b)).mul tendsto_logloglog_div_loglog)
  have h := (tendsto_const_nhds (x := a)).add hsmall
  convert h using 1
  · ext n
    dsimp [upperLoglogEndpoint]
    ring
  · simp

/-- Taking both logarithms, with the truncation from the original theorem.
The extra scalar inequality `1 ≤ U` only ensures the upper bound also covers
`Y < e`; it will be discharged eventually, uniformly in `Y`, below. -/
theorem griffithsStatistic_bounds {n Y c C a b : ℝ}
    (hn : 3 ≤ n) (hc : 0 < c) (hC : 0 < C)
    (hU : 1 ≤ C * (log n) ^ a * (log (log n)) ^ b)
    (hlo : exp (c * (log n / log (log n)) ^ a) ≤ Y)
    (hhi : Y ≤ exp (C * (log n) ^ a * (log (log n)) ^ b)) :
    lowerLoglogEndpoint c a n ≤ griffithsStatistic n Y ∧
      griffithsStatistic n Y ≤ upperLoglogEndpoint C a b n := by
  have hln : 0 < log n := lt_trans zero_lt_one (one_lt_log_of_three_le hn)
  have hll : 0 < log (log n) := log_pos (one_lt_log_of_three_le hn)
  have hbase : 0 < log n / log (log n) := div_pos hln hll
  have hL : 0 < c * (log n / log (log n)) ^ a :=
    mul_pos hc (rpow_pos_of_pos hbase a)
  have hUp : 0 < C * (log n) ^ a * (log (log n)) ^ b :=
    mul_pos (mul_pos hC (rpow_pos_of_pos hln a)) (rpow_pos_of_pos hll b)
  have hmax : 0 < max (exp 1) Y := lt_of_lt_of_le (exp_pos 1) (le_max_left _ _)
  have hlogmax : 1 ≤ log (max (exp 1) Y) := by
    simpa using log_le_log (exp_pos 1) (le_max_left (exp 1) Y)
  have hlow : c * (log n / log (log n)) ^ a ≤ log (max (exp 1) Y) :=
    (le_log_iff_exp_le hmax).mpr (hlo.trans (le_max_right _ _))
  have hupp : log (max (exp 1) Y) ≤ C * (log n) ^ a * (log (log n)) ^ b := by
    apply (log_le_iff_le_exp hmax).mpr
    apply max_le
    · exact exp_le_exp.mpr hU
    · exact hhi
  have hlogL : log (c * (log n / log (log n)) ^ a) =
      log c + a * (log (log n) - log (log (log n))) := by
    rw [log_mul (ne_of_gt hc) (ne_of_gt (rpow_pos_of_pos hbase a)),
      log_rpow hbase, log_div (ne_of_gt hln) (ne_of_gt hll)]
  have hlogU : log (C * (log n) ^ a * (log (log n)) ^ b) =
      log C + a * log (log n) + b * log (log (log n)) := by
    rw [log_mul (ne_of_gt (mul_pos hC (rpow_pos_of_pos hln a)))
      (ne_of_gt (rpow_pos_of_pos hll b)),
      log_mul (ne_of_gt hC) (ne_of_gt (rpow_pos_of_pos hln a)),
      log_rpow hln, log_rpow hll]
  constructor
  · have h := div_le_div_of_nonneg_right (log_le_log hL hlow) hll.le
    rw [hlogL] at h
    convert h using 1 <;> dsimp [lowerLoglogEndpoint, griffithsStatistic]
    field_simp
    <;> ring
  · have h := div_le_div_of_nonneg_right
      (log_le_log (lt_of_lt_of_le zero_lt_one hlogmax) hupp) hll.le
    rw [hlogU] at h
    convert h using 1 <;> dsimp [upperLoglogEndpoint, griffithsStatistic]
    field_simp
    <;> ring

/-- Uniform deterministic form of the double-logarithmic squeeze: the same
threshold in `n` works for every value `Y` satisfying the two exponential bounds. -/
theorem griffithsStatistic_uniform_squeeze {c C a b : ℝ}
    (hc : 0 < c) (hC : 0 < C) (ha : 0 < a) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℝ in atTop, ∀ Y : ℝ,
      exp (c * (log n / log (log n)) ^ a) ≤ Y →
      Y ≤ exp (C * (log n) ^ a * (log (log n)) ^ b) →
      |griffithsStatistic n Y - a| < ε := by
  have hUp := tendsto_upperLoglogEndpoint C a b
  have hLo := tendsto_lowerLoglogEndpoint c a
  have heU : ∀ᶠ n : ℝ in atTop, a / 2 < upperLoglogEndpoint C a b n :=
    hUp.eventually (lt_mem_nhds (by linarith))
  have heL : ∀ᶠ n : ℝ in atTop, a - ε < lowerLoglogEndpoint c a n :=
    hLo.eventually (lt_mem_nhds (by linarith))
  have heR : ∀ᶠ n : ℝ in atTop, upperLoglogEndpoint C a b n < a + ε :=
    hUp.eventually (gt_mem_nhds (by linarith))
  filter_upwards [eventually_ge_atTop (3 : ℝ), heU, heL, heR] with n hn heU heL heR
  have hln : 0 < log n := lt_trans zero_lt_one (one_lt_log_of_three_le hn)
  have hllpos : 0 < log (log n) := log_pos (one_lt_log_of_three_le hn)
  have hUpPos : 0 < C * (log n) ^ a * (log (log n)) ^ b :=
    mul_pos (mul_pos hC (rpow_pos_of_pos hln a)) (rpow_pos_of_pos hllpos b)
  have hlogU : log (C * (log n) ^ a * (log (log n)) ^ b) =
      upperLoglogEndpoint C a b n * log (log n) := by
    rw [log_mul (ne_of_gt (mul_pos hC (rpow_pos_of_pos hln a)))
      (ne_of_gt (rpow_pos_of_pos hllpos b)),
      log_mul (ne_of_gt hC) (ne_of_gt (rpow_pos_of_pos hln a)),
      log_rpow hln, log_rpow hllpos]
    dsimp [upperLoglogEndpoint]
    field_simp
    <;> ring
  have hU : 1 ≤ C * (log n) ^ a * (log (log n)) ^ b := by
    apply (log_nonneg_iff hUpPos).mp
    rw [hlogU]
    exact mul_nonneg (by linarith) hllpos.le
  intro Y hlo hhi
  obtain ⟨hl, hu⟩ := griffithsStatistic_bounds hn hc hC hU hlo hhi
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- The probabilistic implication (1.5) ⇒ (1.6), including the truncation at `e`.
This does not assert the RFIM bounds (1.5): they must be supplied by the separate
rare-region and block-dynamics proofs. The event premise is exactly their
high-probability conclusion, rather than a premise containing the limit. -/
theorem griffithsStatistic_tendstoInMeasure_of_bounds
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (Y : ℕ → Ω → ℝ)
    {c C a b : ℝ} (hc : 0 < c) (hC : 0 < C) (ha : 0 < a)
    (hgood : Tendsto (fun n : ℕ => μ {ω | ¬
      (exp (c * (log (n : ℝ) / log (log (n : ℝ))) ^ a) ≤ Y n ω ∧
        Y n ω ≤ exp (C * (log (n : ℝ)) ^ a * (log (log (n : ℝ))) ^ b))})
      atTop (𝓝 0)) :
    TendstoInMeasure μ (fun (n : ℕ) ω => griffithsStatistic (n : ℝ) (Y n ω)) atTop (fun _ => a) := by
  rw [tendstoInMeasure_iff_dist]
  intro ε hε
  have hevent : ∀ᶠ n : ℕ in atTop, ∀ y : ℝ,
      exp (c * (log (n : ℝ) / log (log (n : ℝ))) ^ a) ≤ y →
      y ≤ exp (C * (log (n : ℝ)) ^ a * (log (log (n : ℝ))) ^ b) →
      |griffithsStatistic n y - a| < ε :=
    tendsto_natCast_atTop_atTop.eventually
      (griffithsStatistic_uniform_squeeze hc hC ha hε)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hgood
    (Eventually.of_forall (fun _ => zero_le _))
  filter_upwards [hevent] with n hn
  apply measure_mono
  intro ω hω
  intro hg
  have h := hn (Y n ω) hg.1 hg.2
  exact (not_lt_of_ge hω) (by simpa only [Real.dist_eq] using h)

/-- Intersecting the good events loses at most the sum of their failure
probabilities; this is the event operation used in the final theorem. -/
theorem failure_intersection_tendsto_zero
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A B : ℕ → Set Ω)
    (hA : Tendsto (fun n => μ (A n)ᶜ) atTop (𝓝 0))
    (hB : Tendsto (fun n => μ (B n)ᶜ) atTop (𝓝 0)) :
    Tendsto (fun n => μ (A n ∩ B n)ᶜ) atTop (𝓝 0) := by
  have hsum : Tendsto (fun n => μ (A n)ᶜ + μ (B n)ᶜ) atTop (𝓝 0) := by
    simpa using hA.add hB
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ => zero_le _)
  intro n
  change μ ((A n ∩ B n)ᶜ) ≤ μ ((A n)ᶜ) + μ ((B n)ᶜ)
  rw [Set.compl_inter]
  exact measure_union_le _ _

end Paper09
