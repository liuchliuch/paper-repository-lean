import Paper08.MomentSeries
import Paper08.ZeroFreeLog
import Paper08.Stability
import Paper08.Moments
import Paper08.Coeff
import Paper08.ModelSupport
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Exact analytic coefficient recurrence

The recurrence is derived from actual holomorphic functions and the identity
`Q' = L' Q`, using uniqueness of analytic power series.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal Topology
open Set Metric Filter

namespace Paper08.LogRecurrence

/-- The ordinary Cauchy product of scalar coefficient sequences. -/
def convolution (a b : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ k ∈ Finset.range (n + 1), a k * b (n - k)

lemma convolution_mul_pow (a b : ℕ → ℂ) (z : ℂ) (n : ℕ) :
    convolution (fun k => a k * z ^ k) (fun k => b k * z ^ k) n =
      convolution a b n * z ^ n := by
  unfold convolution
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hk' : k ≤ n := by have := Finset.mem_range.mp hk; omega
  calc
    a k * z ^ k * (b (n - k) * z ^ (n - k)) = a k * b (n - k) * (z ^ k * z ^ (n - k)) := by ring
    _ = a k * b (n - k) * z ^ n := by rw [← pow_add, Nat.add_sub_of_le hk']

/-- Cauchy multiplication for actual convergent scalar analytic series. -/
theorem hasFPowerSeriesAt_mul {f g : ℂ → ℂ} {a b : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0)
    (hg : HasFPowerSeriesAt g (FormalMultilinearSeries.ofScalars ℂ b) 0) :
    HasFPowerSeriesAt (fun z => f z * g z)
      (FormalMultilinearSeries.ofScalars ℂ (convolution a b)) 0 := by
  obtain ⟨rf, hf⟩ := hf
  obtain ⟨rg, hg⟩ := hg
  obtain ⟨t, htpos, ht⟩ := ENNReal.lt_iff_exists_add_pos_lt.mp (lt_min hf.r_pos hg.r_pos)
  simp only [zero_add] at ht
  have htf := (lt_min_iff.mp ht).1
  have htg := (lt_min_iff.mp ht).2
  have htnorm : ‖(t : ℂ)‖ = (t : ℝ) := by simp
  have hnorm (c : ℕ → ℂ) (hc : (t : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ c).radius) :
      Summable (fun k => ‖c k * (t : ℂ) ^ k‖) := by
    simpa only [norm_mul, norm_pow, htnorm, FormalMultilinearSeries.ofScalars_norm]
      using (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow hc
  have hsumt := summable_norm_sum_mul_range_of_summable_norm
    (hnorm a (htf.trans_le hf.r_le)) (hnorm b (htg.trans_le hg.r_le))
  change Summable (fun n => ‖convolution (fun k => a k * (t : ℂ) ^ k)
    (fun k => b k * (t : ℂ) ^ k) n‖) at hsumt
  have hrad : (t : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ (convolution a b)).radius := by
    apply FormalMultilinearSeries.le_radius_of_summable
    simpa only [convolution_mul_pow, norm_mul, norm_pow, htnorm,
      FormalMultilinearSeries.ofScalars_norm] using hsumt
  refine ⟨t, ⟨hrad, ENNReal.coe_pos.mpr htpos, ?_⟩⟩
  intro z hz
  have hzf : z ∈ EMetric.ball (0 : ℂ) rf := EMetric.ball_subset_ball htf.le hz
  have hzg : z ∈ EMetric.ball (0 : ℂ) rg := EMetric.ball_subset_ball htg.le hz
  have hsf : HasSum (fun k => a k * z ^ k) (f z) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hf.hasSum hzf
  have hsg : HasSum (fun k => b k * z ^ k) (g z) := by
    simpa only [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hg.hasSum hzg
  have hnormz (c : ℕ → ℂ) (hc : (‖z‖₊ : ℝ≥0∞) < (FormalMultilinearSeries.ofScalars ℂ c).radius) :
      Summable (fun k => ‖c k * z ^ k‖) := by
    simpa only [norm_mul, norm_pow, FormalMultilinearSeries.ofScalars_norm]
      using (FormalMultilinearSeries.ofScalars ℂ c).summable_norm_mul_pow hc
  have hzlt : (‖z‖₊ : ℝ≥0∞) < t := by simpa only [mem_emetric_ball_zero_iff, enorm] using hz
  have hh := hasSum_sum_range_mul_of_summable_norm
    (hnormz a (hzlt.trans (htf.trans_le hf.r_le)))
    (hnormz b (hzlt.trans (htg.trans_le hg.r_le)))
  change HasSum (fun n => convolution (fun k => a k * z ^ k) (fun k => b k * z ^ k) n)
    ((∑' k, a k * z ^ k) * ∑' k, b k * z ^ k) at hh
  simpa only [convolution_mul_pow, hsf.tsum_eq, hsg.tsum_eq,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, zero_add] using hh

/-- Differentiating an actual scalar series gives `(n+1) a_(n+1)`. -/
theorem hasFPowerSeriesAt_deriv {f : ℂ → ℂ} {a : ℕ → ℂ}
    (hf : HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ a) 0) :
    HasFPowerSeriesAt (deriv f)
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (n + 1 : ℂ) * a (n + 1))) 0 := by
  obtain ⟨r, hf⟩ := hf
  have hd := (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).comp_hasFPowerSeriesOnBall hf.fderiv
  have heq : (ContinuousLinearMap.apply ℂ ℂ (1 : ℂ)).compFormalMultilinearSeries
      (FormalMultilinearSeries.ofScalars ℂ a).derivSeries =
      FormalMultilinearSeries.ofScalars ℂ (fun n => (n + 1 : ℂ) * a (n + 1)) := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff]
    congr 1
    change (FormalMultilinearSeries.ofScalars ℂ a).derivSeries.coeff n 1 =
      (FormalMultilinearSeries.ofScalars ℂ (fun n => (n + 1 : ℂ) * a (n + 1))).coeff n
    rw [FormalMultilinearSeries.derivSeries_coeff_one, FormalMultilinearSeries.coeff_ofScalars,
      FormalMultilinearSeries.coeff_ofScalars]
    simp [nsmul_eq_mul]
  exact ⟨r, by simpa only [heq, deriv, Function.comp_def] using hd⟩

/-- The exact moment-to-logarithm recurrence over the complex scalars. -/
def Recurrence (M d : ℕ → ℂ) : Prop :=
  d 0 = 0 ∧ ∀ j : ℕ, 1 ≤ j →
    d j = M j - (1 / (j : ℂ)) *
      (∑ i ∈ Finset.range j, (i : ℂ) * d i * M (j - i))

/-- The analytic identity `exp L = Q` forces recurrence (2.15) for the
actual analytic coefficients. Neither the recurrence nor a coefficient
identification is supplied as a hypothesis. -/
theorem recurrence_of_analytic_log {Q L : ℂ → ℂ} {M d : ℕ → ℂ}
    (hQ : HasFPowerSeriesAt Q (FormalMultilinearSeries.ofScalars ℂ M) 0)
    (hL : HasFPowerSeriesAt L (FormalMultilinearSeries.ofScalars ℂ d) 0)
    (hM : M 0 = 1) (hzero : L 0 = 0)
    (hlog : (fun z => Complex.exp (L z)) =ᶠ[𝓝 0] Q) : Recurrence M d := by
  have hD : deriv Q =ᶠ[𝓝 0] (fun z => deriv L z * Q z) := by
    filter_upwards [hlog.deriv, hlog, hL.analyticAt.eventually_analyticAt] with z hd he hl
    have hder := ((Complex.hasDerivAt_exp (L z)).comp z hl.differentiableAt.hasDerivAt).deriv
    change deriv (fun z => Complex.exp (L z)) z = deriv Q z at hd
    change deriv (fun z => Complex.exp (L z)) z = Complex.exp (L z) * deriv L z at hder
    rw [← hd, hder, he]
    ring
  have hdQ := hasFPowerSeriesAt_deriv hQ
  have hdLQ := hasFPowerSeriesAt_mul (hasFPowerSeriesAt_deriv hL) hQ
  have heq := hdQ.eq_formalMultilinearSeries_of_eventually hdLQ hD
  have hcoef : ∀ n : ℕ, (n + 1 : ℂ) * M (n + 1) =
      convolution (fun k => (k + 1 : ℂ) * d (k + 1)) M n := by
    intro n
    have hc := congrArg (fun p : FormalMultilinearSeries ℂ ℂ ℂ => p.coeff n) heq
    simpa only [FormalMultilinearSeries.coeff_ofScalars] using hc
  have hd0 : d 0 = 0 := by
    have hz := hL.coeff_zero (fun _ => 1)
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, hzero] using hz
  refine ⟨hd0, ?_⟩
  intro j hj
  cases j with
  | zero => omega
  | succ n =>
    have hc := hcoef n
    have hs : convolution (fun k => (k + 1 : ℂ) * d (k + 1)) M n =
        (∑ i ∈ Finset.range (n + 1), (i : ℂ) * d i * M (n + 1 - i)) +
          (n + 1 : ℂ) * d (n + 1) := by
      have ht := Finset.sum_range_succ' (fun i => (i : ℂ) * d i * M (n + 1 - i)) (n + 1)
      have ht' := Finset.sum_range_succ (fun i => (i : ℂ) * d i * M (n + 1 - i)) (n + 1)
      simp only [Nat.cast_zero, zero_mul, add_zero, Nat.cast_add, Nat.cast_one,
        Nat.add_sub_add_right, Nat.sub_self, hM, mul_one] at ht ht'
      rw [ht'] at ht
      simpa only [convolution, Nat.add_sub_add_right] using ht.symm
    rw [hs] at hc
    have hn : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    push_cast
    field_simp [hn]
    linear_combination -hc


/-- The exact finite arithmetic algorithm of recurrence (2.15). -/
def output (M : ℕ → ℂ) (j : ℕ) : ℂ :=
  if hj : j = 0 then 0 else
    M j - (1 / (j : ℂ)) * ∑ i : Fin j, (i : ℂ) * output M i * M (j - i)
termination_by j

/-- The recursive arithmetic algorithm satisfies the recurrence by construction. -/
theorem output_recurrence (M : ℕ → ℂ) : Recurrence M (output M) := by
  constructor
  · rw [output]
    simp
  · intro j hj
    rw [output, dif_neg (by omega : j ≠ 0)]
    congr 2
    exact Fin.sum_univ_eq_sum_range (fun i => (i : ℂ) * output M i * M (j - i)) j

/-- Uniqueness follows by induction from already computed lower orders. -/
theorem recurrence_unique {M d e : ℕ → ℂ} (hd : Recurrence M d) (he : Recurrence M e) : d = e := by
  funext j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => exact hd.1.trans he.1.symm
    | succ n =>
      rw [hd.2 (n + 1) (by omega), he.2 (n + 1) (by omega)]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      rw [ih i (Finset.mem_range.mp hi)]

/-- Scalar series represented by Cauchy coefficients of an actual function. -/
theorem hasFPowerSeriesAt_cauchyCoeff {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    HasFPowerSeriesAt f (FormalMultilinearSeries.ofScalars ℂ (Analytic.cauchyCoeff f R)) 0 := by
  lift R to ℝ≥0 using hR.le
  have hp := (hf.hasFPowerSeriesOnBall hR).hasFPowerSeriesAt
  have heq : cauchyPowerSeries f 0 R =
      FormalMultilinearSeries.ofScalars ℂ (Analytic.cauchyCoeff f R) := by
    funext n
    apply ContinuousMultilinearMap.ext
    intro v
    rw [FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.apply_eq_prod_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars]
    rfl
  simpa only [heq] using hp

/-- The exact recurrence output agrees with the actual Cauchy coefficient
of any normalized analytic logarithm. -/
theorem output_eq_cauchyCoeff_of_analytic_log {Q L : ℂ → ℂ} {M : ℕ → ℂ} {R : ℝ}
    (hR : 0 < R)
    (hQ : HasFPowerSeriesAt Q (FormalMultilinearSeries.ofScalars ℂ M) 0)
    (hL : DifferentiableOn ℂ L (closedBall 0 R))
    (hM : M 0 = 1) (hzero : L 0 = 0)
    (hlog : (fun z => Complex.exp (L z)) =ᶠ[𝓝 0] Q) :
    output M = Analytic.cauchyCoeff L R :=
  recurrence_unique (output_recurrence M)
    (recurrence_of_analytic_log hQ (hasFPowerSeriesAt_cauchyCoeff hR hL) hM hzero hlog)

/-- Application to the original integral moments, rather than an unspecified
moment sequence satisfying a certificate. -/
theorem output_moments_eq_log_coeff {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L (closedBall 0 R)) (hzero : L 0 = 0)
    (hlog : (fun z => Complex.exp (L z)) =ᶠ[𝓝 0] ZeroFree.Q E B) :
    output (MomentSeries.moment E B) = Analytic.cauchyCoeff L R :=
  output_eq_cauchyCoeff_of_analytic_log hR (MomentSeries.hasFPowerSeriesAt_Q E B hq hE hLip)
    hL (MomentSeries.moment_zero E B) hzero hlog


/-- The error sequence retained in the finite perturbation polynomial. -/
def truncatedError (δ : ℕ → ℂ) (s : ℕ) (j : ℕ) : ℂ :=
  if 1 ≤ j ∧ j ≤ s then δ j else 0

@[simp] theorem truncatedError_zero (δ : ℕ → ℂ) (s : ℕ) : truncatedError δ s 0 = 0 := by
  simp [truncatedError]

/-- The actual finite polynomial has exactly its stated coefficient sequence. -/
theorem hasFPowerSeriesAt_momentError (δ : ℕ → ℂ) (s : ℕ) :
    HasFPowerSeriesAt (Stability.momentError δ s)
      (FormalMultilinearSeries.ofScalars ℂ (truncatedError δ s)) 0 := by
  apply hasFPowerSeriesAt_iff.mpr
  filter_upwards with z
  have hs : HasSum (fun j => truncatedError δ s j * z ^ j)
      (∑ j ∈ Finset.range (s + 1), truncatedError δ s j * z ^ j) := by
    apply hasSum_sum_of_ne_finset_zero
    intro j hj
    have hj' : ¬j ≤ s := by simp only [Finset.mem_range] at hj; omega
    simp [truncatedError, hj']
  have hsum : (∑ j ∈ Finset.range (s + 1), truncatedError δ s j * z ^ j) =
      Stability.momentError δ s z := by
    rw [Finset.sum_range_succ']
    simp only [truncatedError_zero, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hj' : j + 1 ≤ s := by have := Finset.mem_range.mp hj; omega
    simp [truncatedError, hj']
  rw [hsum] at hs
  simpa only [FormalMultilinearSeries.coeff_ofScalars, smul_eq_mul, zero_add,
    mul_comm] using hs

/-- The exact algorithm depends only on moments through its requested order. -/
theorem output_congr_upto {M N : ℕ → ℂ} {s j : ℕ}
    (hMN : ∀ i, i ≤ s → M i = N i) (hj : j ≤ s) : output M j = output N j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    cases j with
    | zero => exact (output_recurrence M).1.trans (output_recurrence N).1.symm
    | succ n =>
      rw [(output_recurrence M).2 (n + 1) (by omega),
        (output_recurrence N).2 (n + 1) (by omega), hMN (n + 1) hj]
      congr 2
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < n + 1 := Finset.mem_range.mp hi
      rw [ih i hi' (by omega), hMN (n + 1 - i) (by omega)]


/-- Lemma 4.1 for the actual arithmetic recurrence. The only analytic
input bounds the actual underlying function `Q` away from zero; neither
coefficient stability nor the recurrence/analytic identification is assumed. -/
theorem output_stability {Q L : ℂ → ℂ} {M Mtilde : ℕ → ℂ}
    {s j : ℕ} {F κ ξ : ℝ} (hs : 1 ≤ s) (hj : j ≤ s)
    (hκ : 0 ≤ κ) (hF : 4 * Real.exp κ ≤ F) (hξ : 0 ≤ ξ)
    (hprecision : ξ ≤ (F ^ s)⁻¹) (hM : M 0 = 1) (hMt : Mtilde 0 = 1)
    (herrors : ∀ i, 1 ≤ i → i ≤ s → ‖Mtilde i - M i‖ ≤ ξ)
    (hseries : HasFPowerSeriesAt Q (FormalMultilinearSeries.ofScalars ℂ M) 0)
    (hLdiff : DifferentiableOn ℂ L (closedBall 0 (1 / 2))) (hLzero : L 0 = 0)
    (hQdiff : DifferentiableOn ℂ Q (closedBall 0 (1 / 2)))
    (hlog : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Complex.exp (L z) = Q z)
    (hQ : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Real.exp (-(κ * s)) ≤ ‖Q z‖) :
    ‖output Mtilde j - output M j‖ ≤ F ^ s * ξ := by
  let δ : ℕ → ℂ := fun i => Mtilde i - M i
  let T : ℕ → ℂ := fun i => M i + truncatedError δ s i
  let Lhat : ℂ → ℂ := fun z => L z + Stability.logCorrection Q δ s z
  have hsmall := Stability.stability_smallness hs hF hξ hprecision
  have hcorrect := Stability.corrected_logarithm hξ herrors hQdiff hQ hsmall hLdiff hlog
  have hTseries : HasFPowerSeriesAt (fun z => Q z + Stability.momentError δ s z)
      (FormalMultilinearSeries.ofScalars ℂ T) 0 := by
    simpa only [T, ← FormalMultilinearSeries.ofScalars_add, Pi.add_apply] using
      hseries.add (hasFPowerSeriesAt_momentError δ s)
  have hTzero : T 0 = 1 := by simp [T, hM]
  have hLhat0 : Lhat 0 = 0 := by simp [Lhat, Stability.logCorrection, hLzero]
  have hgerm : (fun z => Complex.exp (L z)) =ᶠ[𝓝 0] Q := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
    exact hlog z (ball_subset_closedBall hz)
  have hgermhat : (fun z => Complex.exp (Lhat z)) =ᶠ[𝓝 0]
      (fun z => Q z + Stability.momentError δ s z) := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) (by norm_num : (0 : ℝ) < 1 / 2)] with z hz
    exact hcorrect.2 z (ball_subset_closedBall hz)
  have hMout := output_eq_cauchyCoeff_of_analytic_log (by norm_num : (0 : ℝ) < 1 / 2)
    hseries hLdiff hM hLzero hgerm
  have hTout := output_eq_cauchyCoeff_of_analytic_log (by norm_num : (0 : ℝ) < 1 / 2)
    hTseries hcorrect.1 hTzero hLhat0 hgermhat
  have hTtilde : output Mtilde j = output T j := by
    apply output_congr_upto (s := s) ?_ hj
    intro i hi
    cases i with
    | zero => simp [T, hM, hMt]
    | succ i =>
      change Mtilde (i + 1) = M (i + 1) + truncatedError δ s (i + 1)
      rw [truncatedError, if_pos (show 1 ≤ i + 1 ∧ i + 1 ≤ s from ⟨by omega, hi⟩)]
      dsimp [δ]
      ring
  rw [hTtilde, congrFun hTout j, congrFun hMout j]
  exact Stability.logarithmic_coefficients_difference_stability hs hj hκ hF hξ hprecision
    herrors hLdiff hQdiff hQ

/-- The actual local moment algorithm obeys Lemma 4.1 throughout every
zero-free model disk. The original common disk theorem is the sole remaining
zero-free input; all moment/series/recurrence connections are proved here. -/
theorem actual_moment_recurrence_stability {n r : ℕ} {ι : Type*}
    (E : ι → Factor n r) (B : Finset ι) {q K R S F ξ : ℝ} {s j : ℕ}
    (hq : 0 < q) (hR : 1 < R) (hRS : R < S)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    (hne : ∀ z ∈ ball (0 : ℂ) S, ZeroFree.Q E B z ≠ 0)
    (hB : B.card ≤ s) (hs : 1 ≤ s) (hj : j ≤ s)
    (hF : 4 * Real.exp (Coeff.kappa R q) ≤ F)
    (hprecision : ξ ≤ (F ^ s)⁻¹) (Mtilde : ℕ → ℂ) (hMt : Mtilde 0 = 1)
    (herrors : ∀ i, 1 ≤ i → i ≤ s → ‖Mtilde i - MomentSeries.moment E B i‖ ≤ ξ) :
    ‖output Mtilde j - output (MomentSeries.moment E B) j‖ ≤ F ^ s * ξ := by
  have hξ : 0 ≤ ξ := (norm_nonneg (Mtilde 1 - MomentSeries.moment E B 1)).trans
    (herrors 1 (by omega) hs)
  obtain ⟨L, hLzero, hLdiff, hlog, _, _, hhalf⟩ :=
    Coeff.analytic_bounds_Q_of_nonvanishing E B hq.le hR hRS hE hLip hne
  have hsub : closedBall (0 : ℂ) (1 / 2) ⊆ closedBall 0 R :=
    closedBall_subset_closedBall (by linarith)
  have hκ := (Coeff.kappa_pos hR hq).le
  apply output_stability hs hj hκ hF hξ hprecision
    (MomentSeries.moment_zero E B) hMt herrors
    (MomentSeries.hasFPowerSeriesAt_Q E B hq.le hE hLip)
    (fun z hz => (hLdiff z (hsub hz)).differentiableWithinAt) hLzero
    (ZeroFree.differentiable_Q E B hq.le hE hLip).differentiableOn
    (fun z hz => hlog z (hsub hz))
  intro z hz
  have hz' : ‖z‖ ≤ 1 / 2 := by simpa using hz
  apply le_trans ?_ (hhalf z hz').2
  apply Real.exp_le_exp.mpr
  have hB' : (B.card : ℝ) ≤ s := by exact_mod_cast hB
  nlinarith


/-- The arithmetic recurrence evaluated in the real field, as in the paper. -/
def realOutput (M : ℕ → ℝ) (j : ℕ) : ℝ :=
  if hj : j = 0 then 0 else
    M j - (1 / (j : ℝ)) * ∑ i : Fin j, (i : ℝ) * realOutput M i * M (j - i)
termination_by j

/-- The real algorithm satisfies the paper's existing exact recurrence. -/
theorem realOutput_recurrence (M : ℕ → ℝ) : Moments.Recurrence M (realOutput M) := by
  constructor
  · rw [realOutput]
    simp
  · intro j hj
    rw [realOutput, dif_neg (by omega : j ≠ 0)]
    congr 2
    exact Fin.sum_univ_eq_sum_range (fun i => (i : ℝ) * realOutput M i * M (j - i)) j

/-- Complex analysis leaves the exact real arithmetic algorithm unchanged. -/
theorem ofReal_realOutput (M : ℕ → ℝ) (j : ℕ) :
    (realOutput M j : ℂ) = output (fun i => (M i : ℂ)) j := by
  have hr : Recurrence (fun i => (M i : ℂ)) (fun i => (realOutput M i : ℂ)) := by
    constructor
    · simp only [(realOutput_recurrence M).1, Complex.ofReal_zero]
    · intro i hi
      have h := congrArg Complex.ofReal ((realOutput_recurrence M).2 i hi)
      push_cast at h
      exact h
  exact congrFun (recurrence_unique hr (output_recurrence (fun i => (M i : ℂ)))) j

/-- Lemma 4.1 in the original real arithmetic form, with actual integral
moments and actual recursively computed logarithmic coefficients. -/
theorem actual_real_moment_recurrence_stability {n r : ℕ} {ι : Type*}
    (E : ι → Factor n r) (B : Finset ι) {q K R S F ξ : ℝ} {s j : ℕ}
    (hq : 0 < q) (hR : 1 < R) (hRS : R < S)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    (hne : ∀ z ∈ ball (0 : ℂ) S, ZeroFree.Q E B z ≠ 0)
    (hB : B.card ≤ s) (hs : 1 ≤ s) (hj : j ≤ s)
    (hF : 4 * Real.exp (Coeff.kappa R q) ≤ F)
    (hprecision : ξ ≤ (F ^ s)⁻¹) (Mtilde : ℕ → ℝ) (hMt : Mtilde 0 = 1)
    (herrors : ∀ i, 1 ≤ i → i ≤ s → |Mtilde i - MomentSeries.realMoment E B i| ≤ ξ) :
    |realOutput Mtilde j - realOutput (MomentSeries.realMoment E B) j| ≤ F ^ s * ξ := by
  have herr : ∀ i, 1 ≤ i → i ≤ s →
      ‖(Mtilde i : ℂ) - MomentSeries.moment E B i‖ ≤ ξ := by
    intro i hi his
    rw [← MomentSeries.ofReal_realMoment E B i, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact herrors i hi his
  have h := actual_moment_recurrence_stability E B hq hR hRS hE hLip hne hB hs hj
    hF hprecision (fun i => (Mtilde i : ℂ)) (by simp [hMt]) herr
  have hM : (fun i => (MomentSeries.realMoment E B i : ℂ)) = MomentSeries.moment E B :=
    funext (MomentSeries.ofReal_realMoment E B)
  rw [← hM, ← ofReal_realOutput Mtilde j,
    ← ofReal_realOutput (MomentSeries.realMoment E B) j, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs] at h
  exact h


/-- The real arithmetic algorithm applied to the actual real moments gives
the actual analytic logarithmic coefficient, with no certificate premise. -/
theorem realOutput_moments_eq_log_coeff {n r : ℕ} {ι : Type*} (E : ι → Factor n r)
    (B : Finset ι) {q K R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L (closedBall 0 R)) (hzero : L 0 = 0)
    (hlog : (fun z => Complex.exp (L z)) =ᶠ[𝓝 0] ZeroFree.Q E B) (j : ℕ) :
    (realOutput (MomentSeries.realMoment E B) j : ℂ) = Analytic.cauchyCoeff L R j := by
  rw [ofReal_realOutput]
  have hM : (fun i => (MomentSeries.realMoment E B i : ℂ)) = MomentSeries.moment E B :=
    funext (MomentSeries.ofReal_realMoment E B)
  rw [hM, congrFun (output_moments_eq_log_coeff E B hq hR hE hLip hL hzero hlog) j]

/-- The Taylor error estimate after the actual real recurrence has been
executed on the actual moments. `Q(1)` is the original partition integral;
for the full factor set it equals the partition function by
`ZeroFree.Q_one_eq_partitionFunction`. -/
theorem actual_real_moment_truncation {n r : ℕ} {ι : Type*}
    (E : ι → Factor n r) (B : Finset ι) {q K R S : ℝ}
    (hq : 0 ≤ q) (hR : 1 < R) (hRS : R < S)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    (hne : ∀ z ∈ ball (0 : ℂ) S, ZeroFree.Q E B z ≠ 0) (s : ℕ) :
    |Real.log ‖ZeroFree.Q E B 1‖ -
      ∑ p ∈ Finset.range (s + 1), realOutput (MomentSeries.realMoment E B) p| ≤
        (2 * R * B.card * q / (R - 1)) * R⁻¹ ^ s := by
  obtain ⟨L, hzero, hdiff, hlog, _, htrunc, _⟩ :=
    Coeff.analytic_bounds_Q_of_nonvanishing E B hq hR hRS hE hLip hne
  have hRp : 0 < R := by linarith
  have hLd : DifferentiableOn ℂ L (closedBall 0 R) := fun z hz => (hdiff z hz).differentiableWithinAt
  have hgerm : (fun z => Complex.exp (L z)) =ᶠ[𝓝 0] ZeroFree.Q E B := by
    filter_upwards [Metric.ball_mem_nhds (0 : ℂ) hRp] with z hz
    exact hlog z (ball_subset_closedBall hz)
  have hcoeff := realOutput_moments_eq_log_coeff E B hq hRp hE hLip hLd hzero hgerm
  have hL1 : Real.log ‖ZeroFree.Q E B 1‖ = (L 1).re := by
    rw [← hlog 1 (by simpa using hR.le : (1 : ℂ) ∈ closedBall 0 R),
      Complex.norm_exp, Real.log_exp]
  have hsum : (∑ p ∈ Finset.range (s + 1), Analytic.cauchyCoeff L R p).re =
      ∑ p ∈ Finset.range (s + 1), realOutput (MomentSeries.realMoment E B) p := by
    simp_rw [← hcoeff]
    simp
  have hre := Complex.abs_re_le_norm (L 1 - ∑ p ∈ Finset.range (s + 1), Analytic.cauchyCoeff L R p)
  rw [Complex.sub_re, hsum, ← hL1] at hre
  exact hre.trans (htrunc s)


/-- Diagonal specialization preserves the constant coefficient. -/
theorem coeff_zero_diagonal {ι : Type*} [Fintype ι] (F : MvPowerSeries ι ℝ) :
    PowerSeries.coeff 0 (MultiMoments.diagonalHom ι F) = MvPowerSeries.constantCoeff F := by
  classical
  rw [MultiMoments.coeff_diagonalHom]
  have hindices : MultiMoments.degreeIndices ι 0 = {0} := by
    ext d
    simp [MultiMoments.mem_degreeIndices, Finsupp.degree_eq_zero_iff]
  rw [hindices, Finset.sum_singleton, MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The actual formal logarithm constructed by radial differentiation
satisfies the ordinary scalar logarithmic recurrence after diagonalization. -/
theorem formalLog_scalar_recurrence {ι : Type*} [Fintype ι] [DecidableEq ι]
    (Q : MvPowerSeries ι ℝ) (hQ : MvPowerSeries.constantCoeff Q = 1) :
    Moments.Recurrence (fun j => PowerSeries.coeff j (MultiMoments.diagonalHom ι Q))
      (fun j => PowerSeries.coeff j (MultiMoments.diagonalHom ι (ModelSupport.formalLog Q))) := by
  have hQne : MvPowerSeries.constantCoeff Q ≠ 0 := by rw [hQ]; norm_num
  have hzero : PowerSeries.coeff 0 (MultiMoments.diagonalHom ι (ModelSupport.formalLog Q)) = 0 := by
    rw [coeff_zero_diagonal, ModelSupport.constantCoeff_formalLog]
  constructor
  · exact hzero
  · intro j hj
    have heq := congrArg (fun F => PowerSeries.coeff j (MultiMoments.diagonalHom ι F))
      (ModelSupport.euler_formalLog_mul Q hQne)
    dsimp only at heq
    rw [map_mul, PowerSeries.coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at heq
    simp only [ModelSupport.coeff_diagonal_euler] at heq
    rw [Finset.sum_range_succ] at heq
    simp only [Nat.sub_self, coeff_zero_diagonal, hQ, mul_one] at heq
    have hjne : (j : ℝ) ≠ 0 := by exact_mod_cast (by omega : j ≠ 0)
    field_simp [hjne]
    linear_combination heq

/-- Diagonal formal moment coefficients are exactly the actual real
normalized integral moments. -/
theorem diagonal_momentSeries_eq_realMoment {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) :
    (fun p => PowerSeries.coeff p (MultiMoments.diagonalHom (Fin m)
      (Support.restrictSeries B (MultiMoments.momentSeries E)))) = MomentSeries.realMoment E B := by
  funext p
  apply Complex.ofReal_injective
  exact (MultiMoments.diagonal_momentSeries E B hE hLip p).trans
    (MomentSeries.ofReal_realMoment E B p).symm

/-- The actual formal local logarithmic coefficients satisfy (2.15) for
the actual model integrals, with the recurrence proved rather than assumed. -/
theorem model_logCoeff_recurrence {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) :
    Moments.Recurrence (MomentSeries.realMoment E B) (ModelSupport.logCoeff E B) := by
  have hQ : MvPowerSeries.constantCoeff (Support.restrictSeries B (MultiMoments.momentSeries E)) = 1 := by
    rw [ModelSupport.constantCoeff_restrict, MultiMoments.constantCoeff_momentSeries]
  have h := formalLog_scalar_recurrence (Support.restrictSeries B (MultiMoments.momentSeries E)) hQ
  rw [diagonal_momentSeries_eq_realMoment E B hE hLip] at h
  exact h

/-- Formal local logarithmic coefficients, exact recurrence output, and
actual integral moments are now identified without certificate hypotheses. -/
theorem model_logCoeff_eq_realOutput {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K : ℝ}
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K) :
    ModelSupport.logCoeff E B = realOutput (MomentSeries.realMoment E B) := by
  funext p
  exact Moments.recurrence_unique (model_logCoeff_recurrence E B hE hLip)
    (realOutput_recurrence (MomentSeries.realMoment E B)) p

/-- The formal coefficients used in the connected-support algorithm are
exactly the actual analytic logarithm's Cauchy coefficients. -/
theorem model_logCoeff_eq_analytic_coeff {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K R : ℝ} (hq : 0 ≤ q) (hR : 0 < R)
    (hE : ∀ e ∈ B, (E e).RangeOk q) (hLip : ∀ e ∈ B, (E e).LipOk K)
    {L : ℂ → ℂ} (hL : DifferentiableOn ℂ L (closedBall 0 R)) (hzero : L 0 = 0)
    (hlog : (fun z => Complex.exp (L z)) =ᶠ[𝓝 0] ZeroFree.Q E B) (p : ℕ) :
    (ModelSupport.logCoeff E B p : ℂ) = Analytic.cauchyCoeff L R p := by
  rw [model_logCoeff_eq_realOutput E B hE hLip]
  exact realOutput_moments_eq_log_coeff E B hq hR hE hLip hL hzero hlog p

/-- Equation (2.10) with every local logarithmic coefficient realized by
the actual integral moments and the exact real arithmetic algorithm. -/
theorem connected_support_identity_actual {n r m : ℕ} (E : FactorFamily n r m)
    {q K : ℝ} (hE : ∀ e, (E e).RangeOk q) (hLip : ∀ e, (E e).LipOk K) (p : ℕ) :
    realOutput (MomentSeries.realMoment E Finset.univ) p =
      ∑ A ∈ ((Finset.univ : Finset (Fin m)).powerset.filter fun A : Finset (Fin m) =>
        A.Nonempty ∧ A.card ≤ p ∧ ((Interaction.graph E).induce (A : Set (Fin m))).Connected),
        ∑ B ∈ A.powerset, (-1 : ℝ) ^ (A.card - B.card) *
          realOutput (MomentSeries.realMoment E B) p := by
  classical
  have hbridge : ∀ B, ModelSupport.logCoeff E B = realOutput (MomentSeries.realMoment E B) := by
    intro B
    exact model_logCoeff_eq_realOutput E B (fun e _ => hE e) (fun e _ => hLip e)
  have h := ModelSupport.connected_support_identity E p
  simp_rw [hbridge] at h
  exact h


/-- Lemma 4.1 with the exact local coefficient used in connected-support
assembly, and the approximating coefficient computed by the actual recurrence. -/
theorem model_logCoeff_stability {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K R S F ξ : ℝ} {s j : ℕ}
    (hq : 0 < q) (hR : 1 < R) (hRS : R < S)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    (hne : ∀ z ∈ ball (0 : ℂ) S, ZeroFree.Q E B z ≠ 0)
    (hB : B.card ≤ s) (hs : 1 ≤ s) (hj : j ≤ s)
    (hF : 4 * Real.exp (Coeff.kappa R q) ≤ F)
    (hprecision : ξ ≤ (F ^ s)⁻¹) (Mtilde : ℕ → ℝ) (hMt : Mtilde 0 = 1)
    (herrors : ∀ i, 1 ≤ i → i ≤ s → |Mtilde i - MomentSeries.realMoment E B i| ≤ ξ) :
    |realOutput Mtilde j - ModelSupport.logCoeff E B j| ≤ F ^ s * ξ := by
  rw [model_logCoeff_eq_realOutput E B hE hLip]
  exact actual_real_moment_recurrence_stability E B hq hR hRS hE hLip hne hB hs hj
    hF hprecision Mtilde hMt herrors

/-- Formula (2.3) with the actual local logarithmic coefficients used in
formula (2.10), following their identification with the actual analytic series. -/
theorem model_logCoeff_truncation {n r m : ℕ} (E : FactorFamily n r m)
    (B : Finset (Fin m)) {q K R S : ℝ}
    (hq : 0 ≤ q) (hR : 1 < R) (hRS : R < S)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    (hne : ∀ z ∈ ball (0 : ℂ) S, ZeroFree.Q E B z ≠ 0) (s : ℕ) :
    |Real.log ‖ZeroFree.Q E B 1‖ - ∑ p ∈ Finset.range (s + 1), ModelSupport.logCoeff E B p| ≤
      (2 * R * B.card * q / (R - 1)) * R⁻¹ ^ s := by
  rw [model_logCoeff_eq_realOutput E B hE hLip]
  exact actual_real_moment_truncation E B hq hR hRS hE hLip hne s


end Paper08.LogRecurrence
