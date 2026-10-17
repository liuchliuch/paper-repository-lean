import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic

/-!
# Complex analytic estimates used in Sections 2 and 4

`cauchyCoeff` is an actual coefficient of the Cauchy integral power series,
not an unspecified sequence satisfying a coefficient bound. The estimates
below hold for arbitrary continuous boundary values; analyticity identifies
this series with the original function by `cauchy_series_represents`.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal ComplexConjugate
open Metric Set Complex

namespace Paper08.Analytic

/-- The coefficient of order `j` in the Cauchy integral series at zero. -/
def cauchyCoeff (f : ℂ → ℂ) (R : ℝ) (j : ℕ) : ℂ :=
  cauchyPowerSeries f 0 R j (fun _ => 1)

/-- The Cauchy coefficient estimate, with the radius explicit. -/
theorem norm_cauchyCoeff_le {f : ℂ → ℂ} {R C : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ sphere (0 : ℂ) R, ‖f z‖ ≤ C) (j : ℕ) :
    ‖cauchyCoeff f R j‖ ≤ C * R⁻¹ ^ j := by
  unfold cauchyCoeff
  rw [cauchyPowerSeries_apply]
  have hbound : ∀ z ∈ sphere (0 : ℂ) R,
      ‖(1 / (z - 0)) ^ j • (z - 0)⁻¹ • f z‖ ≤ R⁻¹ ^ j * R⁻¹ * C := by
    intro z hz
    have hz' : ‖z - 0‖ = R := hz
    simp only [norm_smul, norm_pow, norm_inv, hz', one_div]
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hf z hz) (by positivity)
  calc
    ‖(2 * ↑Real.pi * I)⁻¹ • ∮ z in C(0, R), (1 / (z - 0)) ^ j • (z - 0)⁻¹ • f z‖
        ≤ R * (R⁻¹ ^ j * R⁻¹ * C) :=
      circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hbound
    _ = C * R⁻¹ ^ j := by field_simp

/-- For a holomorphic function on the closed disk the Cauchy series is
its analytic power series on the open disk. -/
theorem cauchy_series_represents {f : ℂ → ℂ} {R : ℝ≥0} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) :
    HasFPowerSeriesOnBall f (cauchyPowerSeries f 0 R) 0 R :=
  hf.hasFPowerSeriesOnBall hR

/-- Cauchy's estimate on the fixed half-unit circle used in Lemma 4.1. -/
theorem norm_cauchyCoeff_half_le {f : ℂ → ℂ} {C : ℝ}
    (hf : ∀ z ∈ sphere (0 : ℂ) (1 / 2), ‖f z‖ ≤ C) (j : ℕ) :
    ‖cauchyCoeff f (1 / 2) j‖ ≤ C * 2 ^ j := by
  simpa using norm_cauchyCoeff_le (by norm_num : (0 : ℝ) < 1 / 2) hf j

/-- A normalized analytic logarithm bounds its exponential away from zero. -/
theorem exp_neg_le_norm_of_exp_eq {Q L : ℂ} {A : ℝ}
    (h : Complex.exp L = Q) (hL : ‖L‖ ≤ A) : Real.exp (-A) ≤ ‖Q‖ := by
  rw [← h, Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have := (abs_le.mp (Complex.abs_re_le_norm L)).1
  linarith

/-- Circle averages satisfy the integral triangle inequality. -/
theorem norm_circleAverage_le (f : ℂ → ℂ) (R : ℝ) :
    ‖Real.circleAverage f 0 R‖ ≤ Real.circleAverage (fun z => ‖f z‖) 0 R := by
  unfold Real.circleAverage
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos Real.two_pi_pos]
  exact mul_le_mul_of_nonneg_left
    (intervalIntegral.norm_integral_le_integral_norm Real.two_pi_pos.le) (by positivity)

/-- Cauchy coefficients are the negative-frequency circle averages. -/
theorem cauchyCoeff_eq_circleAverage (f : ℂ → ℂ) {R : ℝ} (hR : 0 < R) (n : ℕ) :
    cauchyCoeff f R n = Real.circleAverage (fun z => z⁻¹ ^ n * f z) 0 R := by
  rw [Real.circleAverage_eq_circleIntegral hR.ne']
  unfold cauchyCoeff
  rw [cauchyPowerSeries_apply]
  congr 2
  funext z
  simp only [sub_zero, one_div, smul_eq_mul]
  ring

/-- Boundary continuity of the weighted values used in coefficient extraction. -/
theorem continuousOn_inv_pow_mul {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (n : ℕ) :
    ContinuousOn (fun z => z⁻¹ ^ n * f z) (sphere 0 R) := by
  have hn : ∀ z ∈ sphere (0 : ℂ) R, z ≠ 0 := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa [mem_sphere_iff_norm] using hz
    exact norm_pos_iff.mp (hz'.symm ▸ hR)
  exact ((continuousOn_id.inv₀ hn).pow n).mul hf

/-- The average of a conjugated holomorphic positive-frequency term
vanishes. This is the Fourier cancellation in Carathéodory's estimate. -/
theorem circleAverage_inv_pow_conj_mul_eq_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ f z) {n : ℕ} (hn : 1 ≤ n) :
    Real.circleAverage (fun z => z⁻¹ ^ n * conj (f z)) 0 R = 0 := by
  have hg : ∀ z ∈ closedBall (0 : ℂ) |R|,
      DifferentiableAt ℂ (fun z => z ^ n * f z) z := by
    intro z hz
    exact (differentiableAt_id.pow n).mul (hf z (by simpa [abs_of_pos hR] using hz))
  have hmean : Real.circleAverage (fun z => z ^ n * f z) 0 R = 0 := by
    rw [circleAverage_of_differentiable_on hg]
    simp [Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hn)]
  have hcont : ContinuousOn (fun z => z ^ n * f z) (sphere 0 |R|) := by
    intro z hz
    exact (hg z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt
  have hconj : Real.circleAverage (fun z => conj (z ^ n * f z)) 0 R = 0 := by
    have h := (Complex.conjCLE.toContinuousLinearMap).circleAverage_comp_comm hcont.circleIntegrable'
    simpa [Function.comp_def, hmean] using h
  calc
    Real.circleAverage (fun z => z⁻¹ ^ n * conj (f z)) 0 R =
        Real.circleAverage (fun z => ((R ^ 2)⁻¹ : ℝ) ^ n • conj (z ^ n * f z)) 0 R := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      have hz' : ‖z‖ = R := by simpa [abs_of_pos hR, mem_sphere_iff_norm] using hz
      dsimp only
      rw [Complex.inv_def, Complex.normSq_eq_norm_sq, hz']
      simp only [mul_pow, map_mul, map_pow, Complex.real_smul, ← Complex.ofReal_pow]
      ring
    _ = ((R ^ 2)⁻¹ : ℝ) ^ n • Real.circleAverage (fun z => conj (z ^ n * f z)) 0 R :=
      Real.circleAverage_fun_smul
    _ = 0 := by rw [hconj, smul_zero]


/-- Nonconstant negative powers have zero circle average. -/
theorem circleAverage_inv_pow_eq_zero {R : ℝ} (hR : 0 < R) {n : ℕ} (hn : 1 ≤ n) :
    Real.circleAverage (fun z : ℂ => z⁻¹ ^ n) 0 R = 0 := by
  simpa using circleAverage_inv_pow_conj_mul_eq_zero (f := fun _ => 1) hR
    (fun _ _ => differentiableAt_const _) hn

/-- The negative Fourier coefficient of the real part is half of the
holomorphic coefficient. -/
theorem circleAverage_inv_pow_realPart {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ f z) {n : ℕ} (hn : 1 ≤ n) :
    Real.circleAverage (fun z => z⁻¹ ^ n * ((f z).re : ℂ)) 0 R =
      (1 / 2 : ℂ) * cauchyCoeff f R n := by
  have hcont : ContinuousOn f (sphere 0 R) :=
    fun z hz => (hf z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt
  have hi := (continuousOn_inv_pow_mul hR hcont n).circleIntegrable hR.le
  have hic := (continuousOn_inv_pow_mul hR
    (Complex.continuous_conj.comp_continuousOn hcont) n).circleIntegrable hR.le
  change CircleIntegrable (fun z => z⁻¹ ^ n * conj (f z)) 0 R at hic
  have heq : (fun z => z⁻¹ ^ n * ((f z).re : ℂ)) =
      (1 / 2 : ℂ) • ((fun z => z⁻¹ ^ n * f z) + (fun z => z⁻¹ ^ n * conj (f z))) := by
    funext z
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul]
    have h := Complex.add_conj (f z)
    push_cast at h
    linear_combination -(z⁻¹ ^ n / 2) * h
  rw [heq, Real.circleAverage_smul, Real.circleAverage_add hi hic,
    circleAverage_inv_pow_conj_mul_eq_zero hR hf hn, add_zero,
    ← cauchyCoeff_eq_circleAverage f hR n, smul_eq_mul]

/-- **Carathéodory's coefficient estimate**. For an actual holomorphic
function vanishing at zero whose real part is at most `A` on the disk,
its coefficient of positive order `n` is bounded by `2 A R⁻ⁿ`.

The proof uses a nonnegative real boundary function and the vanishing
of the conjugate Fourier coefficient. -/
theorem caratheodory_coefficient_bound {f : ℂ → ℂ} {R A : ℝ} (hR : 0 < R)
    (hf : ∀ z ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hzero : f 0 = 0) (hre : ∀ z ∈ closedBall (0 : ℂ) R, (f z).re ≤ A)
    {n : ℕ} (hn : 1 ≤ n) :
    ‖cauchyCoeff f R n‖ ≤ 2 * A * R⁻¹ ^ n := by
  let g : ℂ → ℝ := fun z => A - (f z).re
  have hcont : ContinuousOn f (sphere 0 R) :=
    fun z hz => (hf z (sphere_subset_closedBall hz)).continuousAt.continuousWithinAt
  have hgcont : ContinuousOn g (sphere 0 R) :=
    continuousOn_const.sub (Complex.continuous_re.comp_continuousOn hcont)
  have hinv := (continuousOn_inv_pow_mul hR (continuousOn_const : ContinuousOn (fun _ : ℂ => (1 : ℂ)) (sphere 0 R)) n)
  have hinv' : ContinuousOn (fun z : ℂ => z⁻¹ ^ n) (sphere 0 R) := by simpa using hinv
  have hgre : CircleIntegrable (fun z => z⁻¹ ^ n * ((f z).re : ℂ)) 0 R :=
    (continuousOn_inv_pow_mul hR (Complex.continuous_ofReal.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn hcont)) n).circleIntegrable hR.le
  have hweighted : Real.circleAverage (fun z => z⁻¹ ^ n * (g z : ℂ)) 0 R =
      -(1 / 2 : ℂ) * cauchyCoeff f R n := by
    have heq : (fun z => z⁻¹ ^ n * (g z : ℂ)) =
        (A : ℂ) • (fun z : ℂ => z⁻¹ ^ n) - (fun z : ℂ => z⁻¹ ^ n * ((f z).re : ℂ)) := by
      funext z
      simp only [g, Complex.ofReal_sub, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [heq, Real.circleAverage_sub ((hinv'.circleIntegrable hR.le).const_smul) hgre,
      Real.circleAverage_smul, circleAverage_inv_pow_eq_zero hR hn,
      circleAverage_inv_pow_realPart hR hf hn, smul_zero, zero_sub]
    ring
  have hmean : Real.circleAverage g 0 R = A := by
    have hfint := hcont.circleIntegrable hR.le
    have hmeanf : Real.circleAverage f 0 R = 0 := by
      rw [circleAverage_of_differentiable_on (by simpa [abs_of_pos hR] using hf), hzero]
    have hmeanre : Real.circleAverage (fun z => (f z).re) 0 R = 0 := by
      simpa [Function.comp_def, hmeanf] using Complex.reCLM.circleAverage_comp_comm hfint
    have hire : CircleIntegrable (fun z => (f z).re) 0 R :=
      (Complex.continuous_re.comp_continuousOn hcont).circleIntegrable hR.le
    change Real.circleAverage ((fun _ => A) - fun z => (f z).re) 0 R = A
    rw [Real.circleAverage_sub (circleIntegrable_const A 0 R) hire,
      Real.circleAverage_const, hmeanre, sub_zero]
  have hnormavg : Real.circleAverage (fun z => ‖z⁻¹ ^ n * (g z : ℂ)‖) 0 R = R⁻¹ ^ n * A := by
    calc
      Real.circleAverage (fun z => ‖z⁻¹ ^ n * (g z : ℂ)‖) 0 R =
          Real.circleAverage (fun z => R⁻¹ ^ n • g z) 0 R := by
        apply Real.circleAverage_congr_sphere
        intro z hz
        have hz' : ‖z‖ = R := by simpa [abs_of_pos hR, mem_sphere_iff_norm] using hz
        have hgz : 0 ≤ g z := sub_nonneg.mpr (hre z (by
          apply sphere_subset_closedBall
          simpa [abs_of_pos hR] using hz))
        dsimp only
        rw [norm_mul, norm_pow, norm_inv, hz', Complex.norm_of_nonneg hgz, smul_eq_mul]
      _ = R⁻¹ ^ n • Real.circleAverage g 0 R := Real.circleAverage_fun_smul
      _ = R⁻¹ ^ n * A := by rw [hmean, smul_eq_mul]
  have hnorm := norm_circleAverage_le (fun z => z⁻¹ ^ n * (g z : ℂ)) R
  rw [hweighted, norm_mul, hnormavg] at hnorm
  have hhalf : ‖-(1 / 2 : ℂ)‖ = (1 / 2 : ℝ) := by norm_num
  rw [hhalf] at hnorm
  nlinarith


/-- The scalar Cauchy coefficients sum to the actual holomorphic function. -/
theorem hasSum_cauchyCoeff {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) {z : ℂ} (hz : ‖z‖ < R) :
    HasSum (fun n => cauchyCoeff f R n * z ^ n) (f z) := by
  lift R to ℝ≥0 using hR.le
  have hz' : z ∈ EMetric.ball (0 : ℂ) (R : ℝ≥0∞) := by
    simpa only [mem_emetric_ball_zero_iff, enorm_lt_coe, NNReal.coe_lt_coe] using hz
  have h := (hf.hasFPowerSeriesOnBall hR).hasSum hz'
  simpa only [zero_add, cauchyCoeff, cauchyPowerSeries,
    ContinuousMultilinearMap.mkPiRing_apply, Fin.prod_const, one_pow, one_mul, smul_eq_mul,
    mul_comm] using h

/-- The constant Cauchy coefficient is the value at the center. -/
theorem cauchyCoeff_zero {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (closedBall 0 R)) : cauchyCoeff f R 0 = f 0 := by
  lift R to ℝ≥0 using hR.le
  exact (hf.hasFPowerSeriesOnBall hR).coeff_zero _

/-- The Taylor truncation consequence of Carathéodory's estimate, with
an actual Taylor series and the full geometric remainder. -/
theorem caratheodory_truncation_bound {f : ℂ → ℂ} {R A : ℝ} (hR : 1 < R)
    (hf : ∀ z ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hzero : f 0 = 0) (hre : ∀ z ∈ closedBall (0 : ℂ) R, (f z).re ≤ A) (s : ℕ) :
    ‖f 1 - ∑ p ∈ Finset.range (s + 1), cauchyCoeff f R p‖ ≤
      (2 * A / (R - 1)) * R⁻¹ ^ s := by
  have hRp : 0 < R := by linarith
  have hfd : DifferentiableOn ℂ f (closedBall 0 R) := fun z hz => (hf z hz).differentiableWithinAt
  have hA : 0 ≤ A := by simpa [hzero] using hre 0 (mem_closedBall_self hRp.le)
  have hc0 : cauchyCoeff f R 0 = 0 := by rw [cauchyCoeff_zero hRp hfd, hzero]
  have hcoeff : ∀ n, ‖cauchyCoeff f R n‖ ≤ (2 * A) * R⁻¹ ^ n := by
    intro n
    cases n with
    | zero => simp [hc0, hA]
    | succ n => exact caratheodory_coefficient_bound hRp hf hzero hre (by omega)
  have hsum : HasSum (fun n => cauchyCoeff f R n) (f 1) := by
    simpa only [one_pow, mul_one] using hasSum_cauchyCoeff hRp hfd (by simpa using hR : ‖(1 : ℂ)‖ < R)
  have hr : R⁻¹ < 1 := (inv_lt_one₀ hRp).mpr hR
  have h := norm_sub_le_of_geometric_bound_of_hasSum hr hcoeff hsum (s + 1)
  rw [norm_sub_rev] at h
  convert h using 1
  rw [pow_succ]
  field_simp


/-- On the half-unit disk, the same actual Taylor series gives the
logarithm bound used for the denominator in Lemma 4.1. -/
theorem caratheodory_half_disk_bound {f : ℂ → ℂ} {R A : ℝ} (hR : 1 < R)
    (hf : ∀ z ∈ closedBall (0 : ℂ) R, DifferentiableAt ℂ f z)
    (hzero : f 0 = 0) (hre : ∀ z ∈ closedBall (0 : ℂ) R, (f z).re ≤ A)
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) : ‖f z‖ ≤ 2 * A / (2 * R - 1) := by
  have hRp : 0 < R := by linarith
  have hfd : DifferentiableOn ℂ f (closedBall 0 R) := fun w hw => (hf w hw).differentiableWithinAt
  have hA : 0 ≤ A := by simpa [hzero] using hre 0 (mem_closedBall_self hRp.le)
  have hc0 : cauchyCoeff f R 0 = 0 := by rw [cauchyCoeff_zero hRp hfd, hzero]
  have hsum := hasSum_cauchyCoeff hRp hfd (lt_of_le_of_lt hz (by linarith))
  have hsum' : HasSum (fun n => cauchyCoeff f R (n + 1) * z ^ (n + 1)) (f z) := by
    simpa only [Finset.range_one, Finset.sum_singleton, hc0, zero_mul, sub_zero] using
      (hasSum_nat_add_iff' 1).mpr hsum
  let r : ℝ := (2 * R)⁻¹
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hr1 : r < 1 := by
    dsimp [r]
    apply (inv_lt_one₀ (by positivity)).mpr
    linarith
  have hterm : ∀ n, ‖cauchyCoeff f R (n + 1) * z ^ (n + 1)‖ ≤ (2 * A * r) * r ^ n := by
    intro n
    rw [norm_mul, norm_pow]
    calc
      ‖cauchyCoeff f R (n + 1)‖ * ‖z‖ ^ (n + 1) ≤
          (2 * A * R⁻¹ ^ (n + 1)) * (1 / (2 : ℝ)) ^ (n + 1) :=
        mul_le_mul (caratheodory_coefficient_bound hRp hf hzero hre (by omega))
          (pow_le_pow_left₀ (norm_nonneg z) hz _) (by positivity) (by positivity)
      _ = (2 * A * r) * r ^ n := by
        rw [mul_assoc, ← mul_pow]
        have hid : R⁻¹ * (1 / (2 : ℝ)) = r := by dsimp [r]; field_simp
        rw [hid, pow_succ]
        ring
  have hb := hsum'.norm_le_of_bounded
    ((hasSum_geometric_of_lt_one hr0 hr1).mul_left (2 * A * r)) hterm
  convert hb using 1
  dsimp [r]
  field_simp


/-- Linearity of the actual Cauchy coefficient under addition. -/
theorem cauchyCoeff_add {f g : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (sphere 0 R)) (hg : ContinuousOn g (sphere 0 R)) (n : ℕ) :
    cauchyCoeff (fun z => f z + g z) R n = cauchyCoeff f R n + cauchyCoeff g R n := by
  rw [cauchyCoeff_eq_circleAverage _ hR, cauchyCoeff_eq_circleAverage f hR,
    cauchyCoeff_eq_circleAverage g hR]
  have heq : (fun z => z⁻¹ ^ n * (f z + g z)) =
      (fun z => z⁻¹ ^ n * f z) + (fun z => z⁻¹ ^ n * g z) := by
    ext z
    simp [mul_add]
  rw [heq, Real.circleAverage_add
    ((continuousOn_inv_pow_mul hR hf n).circleIntegrable hR.le)
    ((continuousOn_inv_pow_mul hR hg n).circleIntegrable hR.le)]


end Paper08.Analytic
