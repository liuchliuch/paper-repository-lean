import Paper08.Analytic

/-!
# The analytic perturbation argument of Lemma 4.1

The perturbation below is built from the actual moment errors. We prove its
uniform norm bound, nonvanishing of the perturbed function, holomorphy of
the logarithmic correction, and the exponential coefficient stability
bound. The lower bound on `Q` is the analytic lower bound required from
Lemma 2.2; this file does not claim to prove that bound from the factor
model or identify the coefficients with recurrence (2.15).
-/

noncomputable section
open scoped BigOperators NNReal
open Metric Set Complex

namespace Paper08.Stability
open Paper08.Analytic

/-- The polynomial `E_B` of the proof of Lemma 4.1, with no constant term. -/
def momentError (δ : ℕ → ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range s, δ (i + 1) * z ^ (i + 1)

@[simp] theorem momentError_zero (δ : ℕ → ℂ) (s : ℕ) : momentError δ s 0 = 0 := by
  simp [momentError]

/-- The geometric weights of the error polynomial sum to at most one. -/
theorem sum_half_powers_le_one (s : ℕ) :
    (∑ i ∈ Finset.range s, (1 / (2 : ℝ)) ^ (i + 1)) ≤ 1 := by
  have h := sum_geometric_two_le s
  simpa [pow_succ, ← Finset.sum_mul] using mul_le_mul_of_nonneg_right h (by norm_num : (0 : ℝ) ≤ 1 / 2)

/-- Moment errors of size `ξ` give a uniform error at most `ξ` on the
closed half-unit disk, independently of the moment order. -/
theorem norm_momentError_le {δ : ℕ → ℂ} {s : ℕ} {ξ : ℝ} (hξ : 0 ≤ ξ)
    (hδ : ∀ j, 1 ≤ j → j ≤ s → ‖δ j‖ ≤ ξ) {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖momentError δ s z‖ ≤ ξ := by
  calc
    ‖momentError δ s z‖ ≤ ∑ i ∈ Finset.range s, ‖δ (i + 1) * z ^ (i + 1)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ Finset.range s, ξ * (1 / (2 : ℝ)) ^ (i + 1) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_mul, norm_pow]
      exact mul_le_mul (hδ (i + 1) (by omega) (by simpa using Finset.mem_range.mp hi))
        (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity) hξ
    _ = ξ * ∑ i ∈ Finset.range s, (1 / (2 : ℝ)) ^ (i + 1) := by rw [Finset.mul_sum]
    _ ≤ ξ * 1 := mul_le_mul_of_nonneg_left (sum_half_powers_le_one s) hξ
    _ = ξ := mul_one ξ

/-- The error polynomial is entire. -/
theorem differentiable_momentError (δ : ℕ → ℂ) (s : ℕ) :
    Differentiable ℂ (momentError δ s) := by
  unfold momentError
  fun_prop

/-- The analytic logarithmic correction for `Q + E`. -/
def logCorrection (Q : ℂ → ℂ) (δ : ℕ → ℂ) (s : ℕ) (z : ℂ) : ℂ :=
  Complex.log (1 + momentError δ s z / Q z)

/-- The ratio `E/Q` is small when `Q` is bounded away from zero. -/
theorem norm_error_ratio_le {Q : ℂ → ℂ} {δ : ℕ → ℂ} {s : ℕ} {ξ A : ℝ}
    (hξ : 0 ≤ ξ) (hδ : ∀ j, 1 ≤ j → j ≤ s → ‖δ j‖ ≤ ξ)
    (hQ : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Real.exp (-A) ≤ ‖Q z‖)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (1 / 2)) :
    ‖momentError δ s z / Q z‖ ≤ Real.exp A * ξ := by
  have hz' : ‖z‖ ≤ 1 / 2 := by simpa using hz
  rw [norm_div]
  calc
    ‖momentError δ s z‖ / ‖Q z‖ ≤ ξ / Real.exp (-A) :=
      div_le_div₀ hξ (norm_momentError_le hξ hδ hz') (Real.exp_pos _) (hQ z hz)
    _ = Real.exp A * ξ := by rw [Real.exp_neg, div_inv_eq_mul]; ring

/-- For sufficiently small moments, the perturbed function is nonzero
and its logarithmic correction is uniformly bounded. -/
theorem analytic_logCorrection {Q : ℂ → ℂ} {δ : ℕ → ℂ} {s : ℕ} {ξ A : ℝ}
    (hξ : 0 ≤ ξ) (hδ : ∀ j, 1 ≤ j → j ≤ s → ‖δ j‖ ≤ ξ)
    (hQdiff : DifferentiableOn ℂ Q (closedBall 0 (1 / 2)))
    (hQ : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Real.exp (-A) ≤ ‖Q z‖)
    (hsmall : Real.exp A * ξ ≤ 1 / 4) :
    DifferentiableOn ℂ (logCorrection Q δ s) (closedBall 0 (1 / 2)) ∧
    (∀ z ∈ closedBall (0 : ℂ) (1 / 2),
      Q z + momentError δ s z ≠ 0 ∧
      Complex.exp (logCorrection Q δ s z) = 1 + momentError δ s z / Q z ∧
      ‖logCorrection Q δ s z‖ ≤ 2 * Real.exp A * ξ) := by
  have hnonzero : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Q z ≠ 0 := by
    intro z hz
    exact norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) (hQ z hz))
  have hratio : ∀ z ∈ closedBall (0 : ℂ) (1 / 2),
      ‖momentError δ s z / Q z‖ ≤ 1 / 4 := by
    intro z hz
    exact (norm_error_ratio_le hξ hδ hQ hz).trans hsmall
  have hslit : ∀ z ∈ closedBall (0 : ℂ) (1 / 2),
      1 + momentError δ s z / Q z ∈ Complex.slitPlane := by
    intro z hz
    exact Complex.mem_slitPlane_of_norm_lt_one (lt_of_le_of_lt (hratio z hz) (by norm_num))
  constructor
  · unfold logCorrection
    exact (DifferentiableOn.const_add 1 ((differentiable_momentError δ s).differentiableOn.div hQdiff hnonzero)).clog hslit
  · intro z hz
    have hr := hratio z hz
    have hr' : ‖momentError δ s z / Q z‖ ≤ 1 / 2 := by linarith
    have hlog := Complex.norm_log_one_add_half_le_self hr'
    refine ⟨?_, Complex.exp_log (Complex.slitPlane_ne_zero (hslit z hz)), ?_⟩
    · have hmul : Q z + momentError δ s z = Q z * (1 + momentError δ s z / Q z) := by
        field_simp [hnonzero z hz]
      rw [hmul]
      exact mul_ne_zero (hnonzero z hz) (Complex.slitPlane_ne_zero (hslit z hz))
    · unfold logCorrection
      have hb := norm_error_ratio_le hξ hδ hQ hz
      have ha := mul_nonneg (Real.exp_pos A).le hξ
      nlinarith

/-- Cauchy's estimate applied to the actual analytic logarithmic
correction. No coefficient-error assumption is used. -/
theorem norm_logCorrection_coeff_le {Q : ℂ → ℂ} {δ : ℕ → ℂ} {s : ℕ} {ξ A : ℝ}
    (hξ : 0 ≤ ξ) (hδ : ∀ j, 1 ≤ j → j ≤ s → ‖δ j‖ ≤ ξ)
    (hQdiff : DifferentiableOn ℂ Q (closedBall 0 (1 / 2)))
    (hQ : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Real.exp (-A) ≤ ‖Q z‖)
    (hsmall : Real.exp A * ξ ≤ 1 / 4) (j : ℕ) :
    ‖cauchyCoeff (logCorrection Q δ s) (1 / 2) j‖ ≤
      2 ^ (j + 1) * Real.exp A * ξ := by
  have hc := (analytic_logCorrection hξ hδ hQdiff hQ hsmall).2
  calc
    ‖cauchyCoeff (logCorrection Q δ s) (1 / 2) j‖ ≤ (2 * Real.exp A * ξ) * 2 ^ j :=
      norm_cauchyCoeff_half_le (fun z hz => (hc z (sphere_subset_closedBall hz)).2.2) j
    _ = 2 ^ (j + 1) * Real.exp A * ξ := by ring

/-- The fixed choice `F ≥ 4 exp κ` makes the relative perturbation at
most `4⁻ˢ`, and hence at most one quarter for positive `s`. -/
theorem stability_smallness {F κ ξ : ℝ} {s : ℕ} (hs : 1 ≤ s)
    (hF : 4 * Real.exp κ ≤ F) (_hξ : 0 ≤ ξ) (hprecision : ξ ≤ (F ^ s)⁻¹) :
    Real.exp (κ * s) * ξ ≤ 1 / 4 := by
  have hFp : 0 < F := lt_of_lt_of_le (by positivity) hF
  have hratio : Real.exp κ / F ≤ 1 / 4 := by
    apply (div_le_iff₀ hFp).mpr
    linarith
  calc
    Real.exp (κ * s) * ξ = Real.exp κ ^ s * ξ := by rw [mul_comm κ, Real.exp_nat_mul]
    _ ≤ Real.exp κ ^ s * (F ^ s)⁻¹ := mul_le_mul_of_nonneg_left hprecision (by positivity)
    _ = (Real.exp κ / F) ^ s := by rw [div_pow, div_eq_mul_inv]
    _ ≤ (1 / (4 : ℝ)) ^ s := pow_le_pow_left₀ (by positivity) hratio s
    _ ≤ (1 / (4 : ℝ)) ^ 1 := pow_le_pow_of_le_one (by norm_num) (by norm_num) hs
    _ = 1 / 4 := pow_one _

/-- The numerical absorption of the Cauchy factor into `Fˢ`. -/
theorem stability_constant_bound {F κ ξ : ℝ} {s j : ℕ} (hs : 1 ≤ s) (hj : j ≤ s)
    (hκ : 0 ≤ κ) (hF : 4 * Real.exp κ ≤ F) (hξ : 0 ≤ ξ) :
    2 ^ (j + 1) * Real.exp (κ * s) * ξ ≤ F ^ s * ξ := by
  have hexp : 1 ≤ Real.exp κ := Real.one_le_exp_iff.mpr hκ
  have hs' : j + 1 ≤ s + s := by omega
  have hpow : (2 : ℝ) ^ (j + 1) ≤ 4 ^ s := by
    calc
      (2 : ℝ) ^ (j + 1) ≤ 2 ^ (s + s) := pow_le_pow_right₀ (by norm_num) hs'
      _ = 4 ^ s := by rw [pow_add, ← mul_pow]; norm_num
  apply mul_le_mul_of_nonneg_right ?_ hξ
  calc
    2 ^ (j + 1) * Real.exp (κ * s) ≤ 4 ^ s * Real.exp (κ * s) :=
      mul_le_mul_of_nonneg_right hpow (Real.exp_pos _).le
    _ = (4 * Real.exp κ) ^ s := by rw [mul_comm κ, Real.exp_nat_mul, mul_pow]
    _ ≤ F ^ s := pow_le_pow_left₀ (by positivity) hF s

/-- The analytic coefficient stability asserted in the middle of the
proof of Lemma 4.1. The coefficient here is extracted from the actual
holomorphic logarithmic correction to `Q`, and `δ` is the actual moment
error sequence. -/
theorem local_logarithmic_coefficients_stability
    {Q : ℂ → ℂ} {δ : ℕ → ℂ} {s j : ℕ} {F κ ξ : ℝ}
    (hs : 1 ≤ s) (hj : j ≤ s) (hκ : 0 ≤ κ) (hF : 4 * Real.exp κ ≤ F)
    (hξ : 0 ≤ ξ) (hprecision : ξ ≤ (F ^ s)⁻¹)
    (hδ : ∀ i, 1 ≤ i → i ≤ s → ‖δ i‖ ≤ ξ)
    (hQdiff : DifferentiableOn ℂ Q (closedBall 0 (1 / 2)))
    (hQ : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Real.exp (-(κ * s)) ≤ ‖Q z‖) :
    ‖cauchyCoeff (logCorrection Q δ s) (1 / 2) j‖ ≤ F ^ s * ξ :=
  (norm_logCorrection_coeff_le hξ hδ hQdiff hQ
    (stability_smallness hs hF hξ hprecision) j).trans
      (stability_constant_bound hs hj hκ hF hξ)

/-- Adding the correction to any analytic logarithm of `Q` gives an
actual analytic logarithm of the perturbed function. -/
theorem corrected_logarithm {Q L : ℂ → ℂ} {δ : ℕ → ℂ} {s : ℕ} {ξ A : ℝ}
    (hξ : 0 ≤ ξ) (hδ : ∀ j, 1 ≤ j → j ≤ s → ‖δ j‖ ≤ ξ)
    (hQdiff : DifferentiableOn ℂ Q (closedBall 0 (1 / 2)))
    (hQ : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Real.exp (-A) ≤ ‖Q z‖)
    (hsmall : Real.exp A * ξ ≤ 1 / 4)
    (hLdiff : DifferentiableOn ℂ L (closedBall 0 (1 / 2)))
    (hL : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Complex.exp (L z) = Q z) :
    DifferentiableOn ℂ (fun z => L z + logCorrection Q δ s z) (closedBall 0 (1 / 2)) ∧
      ∀ z ∈ closedBall (0 : ℂ) (1 / 2),
        Complex.exp (L z + logCorrection Q δ s z) = Q z + momentError δ s z := by
  have hc := analytic_logCorrection hξ hδ hQdiff hQ hsmall
  refine ⟨hLdiff.fun_add hc.1, ?_⟩
  intro z hz
  rw [Complex.exp_add, hL z hz, (hc.2 z hz).2.1]
  have hn : Q z ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le (Real.exp_pos _) (hQ z hz))
  field_simp


/-- The actual logarithms, before and after perturbation, have coefficient
difference bounded by `Fˢ ξ`. The corrected logarithm is the one constructed
in `corrected_logarithm`; its coefficients are extracted by Cauchy integrals.
Identification with the finite recurrence remains a separate obligation. -/
theorem logarithmic_coefficients_difference_stability
    {Q L : ℂ → ℂ} {δ : ℕ → ℂ} {s j : ℕ} {F κ ξ : ℝ}
    (hs : 1 ≤ s) (hj : j ≤ s) (hκ : 0 ≤ κ) (hF : 4 * Real.exp κ ≤ F)
    (hξ : 0 ≤ ξ) (hprecision : ξ ≤ (F ^ s)⁻¹)
    (hδ : ∀ i, 1 ≤ i → i ≤ s → ‖δ i‖ ≤ ξ)
    (hLdiff : DifferentiableOn ℂ L (closedBall 0 (1 / 2)))
    (hQdiff : DifferentiableOn ℂ Q (closedBall 0 (1 / 2)))
    (hQ : ∀ z ∈ closedBall (0 : ℂ) (1 / 2), Real.exp (-(κ * s)) ≤ ‖Q z‖) :
    ‖cauchyCoeff (fun z => L z + logCorrection Q δ s z) (1 / 2) j -
      cauchyCoeff L (1 / 2) j‖ ≤ F ^ s * ξ := by
  have hcd := (analytic_logCorrection hξ hδ hQdiff hQ
    (stability_smallness hs hF hξ hprecision)).1
  rw [cauchyCoeff_add (by norm_num : (0 : ℝ) < 1 / 2)
    (hLdiff.continuousOn.mono sphere_subset_closedBall)
    (hcd.continuousOn.mono sphere_subset_closedBall), add_sub_cancel_left]
  exact local_logarithmic_coefficients_stability hs hj hκ hF hξ hprecision hδ hQdiff hQ


end Paper08.Stability
