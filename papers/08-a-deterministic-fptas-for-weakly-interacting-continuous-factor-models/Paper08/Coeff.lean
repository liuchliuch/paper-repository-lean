import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Paper08.Basic
import Paper08.Analytic
import Paper08.ZeroFreeLog

/-!
# The analytic estimates of Lemma 2.2

The actual Carathéodory estimate, Taylor remainder and half-disk bounds
are proved in `Paper08.Analytic` and instantiated here for normalized
analytic logarithms of the original integral `ZeroFree.Q`.

`analytic_bounds_Q_of_nonvanishing` proves this entire analytic implication
from nonvanishing on a slightly larger disk. The original common zero-free
disk (Lemma 2.1) remains a separate mathematical obligation. This file also
retains the elementary constants and error-splitting lemmas used elsewhere.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace Coeff

/-- The constant `κ = 2 R q / (2 R - 1)` of (2.4). -/
def kappa (R q : ℝ) : ℝ := 2 * R * q / (2 * R - 1)

lemma kappa_pos {R q : ℝ} (hR : 1 < R) (hq : 0 < q) : 0 < kappa R q := by
  unfold kappa
  apply div_pos
  · positivity
  · linarith

/-- `2 R h q / (2 R - 1) = κ h` — the series sum in (2.4). -/
lemma kappa_eq (R q h : ℝ) : 2 * R * h * q / (2 * R - 1) = kappa R q * h := by
  unfold kappa
  ring

/-- On `|z| ≤ 1/2` the logarithm satisfies `|L_B| ≤ κ h`, and hence
`|Q_B| = exp(Re L_B) ≥ exp(-κ h)`.  Monotonicity step of (2.4). -/
lemma exp_neg_le_of_log_abs {Q : ℝ} (hQ : 0 < Q) {κ h : ℝ}
    (hlog : Real.log Q ≥ -(κ * h)) :
    Q ≥ Real.exp (-(κ * h)) := by
  rw [← Real.exp_log hQ]
  exact Real.exp_le_exp.mpr hlog

/-- Coefficient-tail model of (2.2)–(2.3): the bound is nonnegative. -/
lemma coeff_tail_nonneg {R h q : ℝ} (hR : 1 < R) (hq : 0 < q) (hh : 0 ≤ h) :
    0 ≤ 2 * R * h * q / (R - 1) := by
  apply div_nonneg
  · positivity
  · linarith

/-- Triangle inequality `|a + b| ≤ |a| + |b|`. -/
lemma abs_add_le (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h1 : a + b ≤ |a| + |b| := add_le_add (le_abs_self a) (le_abs_self b)
  have h2 : -( |a| + |b| ) ≤ a + b := by
    have ha : -|a| ≤ a := neg_abs_le a
    have hb : -|b| ≤ b := neg_abs_le b
    linarith
  exact abs_le.mpr ⟨h2, h1⟩

/-- Three-term accuracy split of Theorem 1.2. -/
lemma three_term_split {w x y z ε : ℝ}
    (h1 : |w - x| ≤ ε / 3) (h2 : |x - y| ≤ ε / 3) (h3 : |y - z| ≤ ε / 3) :
    |w - z| ≤ ε := by
  have hsum : w - z = (w - x) + (x - y) + (y - z) := by ring
  rw [hsum]
  have h12 : |(w - x) + (x - y)| ≤ |w - x| + |x - y| := abs_add_le _ _
  have h123 : |(w - x) + (x - y) + (y - z)| ≤ |(w - x) + (x - y)| + |y - z| := abs_add_le _ _
  nlinarith [abs_le.mp h1 |>.2, abs_le.mp h2 |>.2, abs_le.mp h3 |>.2,
    abs_nonneg (w - x), abs_nonneg (x - y), abs_nonneg (y - z)]

/-- Taylor remainder bound used in the last step of §4. -/
lemma taylor_rational_bound (N : ℕ) : (0 : ℝ) ≤ 1 / (Nat.factorial N : ℝ) := by
  positivity

/-- `log` is monotone on `(0,∞)` — the step `|log P_N(t) - t|` after
`|P_N(t) - e^t| ≤ a` uses that `exp` is increasing. -/
lemma log_mono {x y : ℝ} (hx : 0 < x) (h : x ≤ y) : Real.log x ≤ Real.log y :=
  Real.log_le_log hx h

/-- The real-part bound for any actual analytic logarithm follows from
the exponential bound on its underlying partition function. -/
theorem realPart_log_le_of_norm_bound {L Q : ℂ → ℂ} {R A : ℝ}
    (hlog : ∀ z ∈ Metric.closedBall (0 : ℂ) R, Complex.exp (L z) = Q z)
    (hQ : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖Q z‖ ≤ Real.exp A) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) R, (L z).re ≤ A := by
  intro z hz
  apply Real.exp_le_exp.mp
  rw [← Complex.norm_exp, hlog z hz]
  exact hQ z hz

/-- The complete analytic implication (2.2): the coefficient is the
actual Cauchy integral coefficient of the normalized logarithm. -/
theorem coefficient_bound_of_analytic_log {L Q : ℂ → ℂ} {R h q : ℝ}
    (hR : 1 < R)
    (hL : ∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ L z)
    (hzero : L 0 = 0)
    (hlog : ∀ z ∈ Metric.closedBall (0 : ℂ) R, Complex.exp (L z) = Q z)
    (hQ : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖Q z‖ ≤ Real.exp (R * h * q))
    {p : ℕ} (hp : 1 ≤ p) :
    ‖Analytic.cauchyCoeff L R p‖ ≤ 2 * R * h * q * R⁻¹ ^ p := by
  convert Analytic.caratheodory_coefficient_bound (by linarith : 0 < R) hL hzero
    (realPart_log_le_of_norm_bound hlog hQ) hp using 1; ring

/-- The complete analytic implication (2.3), with the actual value of
the logarithm and its actual Taylor coefficients. -/
theorem truncation_bound_of_analytic_log {L Q : ℂ → ℂ} {R h q : ℝ}
    (hR : 1 < R)
    (hL : ∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ L z)
    (hzero : L 0 = 0)
    (hlog : ∀ z ∈ Metric.closedBall (0 : ℂ) R, Complex.exp (L z) = Q z)
    (hQ : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖Q z‖ ≤ Real.exp (R * h * q)) (s : ℕ) :
    ‖L 1 - ∑ p ∈ Finset.range (s + 1), Analytic.cauchyCoeff L R p‖ ≤
      (2 * R * h * q / (R - 1)) * R⁻¹ ^ s := by
  convert Analytic.caratheodory_truncation_bound hR hL hzero
    (realPart_log_le_of_norm_bound hlog hQ) s using 1; ring

/-- The complete analytic implication (2.4): the normalized logarithm
is bounded on the half disk and its exponential is bounded away from zero.
Construction of that logarithm from the original model's zero-free disk
is a separate mathematical obligation. -/
theorem half_disk_bound_of_analytic_log {L Q : ℂ → ℂ} {R h q : ℝ}
    (hR : 1 < R)
    (hL : ∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ L z)
    (hzero : L 0 = 0)
    (hlog : ∀ z ∈ Metric.closedBall (0 : ℂ) R, Complex.exp (L z) = Q z)
    (hQ : ∀ z ∈ Metric.closedBall (0 : ℂ) R, ‖Q z‖ ≤ Real.exp (R * h * q))
    {z : ℂ} (hz : ‖z‖ ≤ 1 / 2) :
    ‖L z‖ ≤ kappa R q * h ∧ Real.exp (-(kappa R q * h)) ≤ ‖Q z‖ := by
  have hbound : ‖L z‖ ≤ kappa R q * h := by
    convert Analytic.caratheodory_half_disk_bound hR hL hzero
      (realPart_log_le_of_norm_bound hlog hQ) hz using 1
    unfold kappa
    ring
  refine ⟨hbound, Analytic.exp_neg_le_norm_of_exp_eq (hlog z ?_) hbound⟩
  simpa only [Metric.mem_closedBall, dist_zero_right] using
    (le_trans hz (by linarith : (1 / 2 : ℝ) ≤ R))


/-- Application of the analytic estimates to the original partition
integral. The common zero-free disk is the explicit remaining hypothesis;
all analytic logarithm construction, coefficient bounds, Taylor remainder,
and half-disk lower bounds are proved from it and the model's original
range and Lipschitz hypotheses. -/
theorem analytic_bounds_Q_of_nonvanishing {n r : ℕ} {ι : Type*}
    (E : ι → Factor n r) (B : Finset ι) {q K R S : ℝ}
    (hq : 0 ≤ q) (hR : 1 < R) (hRS : R < S)
    (hE : ∀ i ∈ B, (E i).RangeOk q) (hLip : ∀ i ∈ B, (E i).LipOk K)
    (hne : ∀ z ∈ Metric.ball (0 : ℂ) S, ZeroFree.Q E B z ≠ 0) :
    ∃ L : ℂ → ℂ, L 0 = 0 ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ L z) ∧
      (∀ z ∈ Metric.closedBall (0 : ℂ) R, Complex.exp (L z) = ZeroFree.Q E B z) ∧
      (∀ p : ℕ, 1 ≤ p → ‖Analytic.cauchyCoeff L R p‖ ≤
        2 * R * B.card * q * R⁻¹ ^ p) ∧
      (∀ s : ℕ, ‖L 1 - ∑ p ∈ Finset.range (s + 1), Analytic.cauchyCoeff L R p‖ ≤
        (2 * R * B.card * q / (R - 1)) * R⁻¹ ^ s) ∧
      (∀ z : ℂ, ‖z‖ ≤ 1 / 2 → ‖L z‖ ≤ kappa R q * B.card ∧
        Real.exp (-(kappa R q * B.card)) ≤ ‖ZeroFree.Q E B z‖) := by
  have hS : 0 < S := by linarith
  obtain ⟨L, hzero, hLdiff, hLderiv, hlog⟩ :=
    ZeroFree.exists_normalized_log_Q E B hq hS hE hLip hne
  have hsub : Metric.closedBall (0 : ℂ) R ⊆ Metric.ball 0 S :=
    Metric.closedBall_subset_ball hRS
  have hLd : ∀ z ∈ Metric.closedBall (0 : ℂ) R, DifferentiableAt ℂ L z :=
    fun z hz => (hLderiv z (hsub hz)).differentiableAt
  have hLe : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      Complex.exp (L z) = ZeroFree.Q E B z := fun z hz => hlog z (hsub hz)
  have hQbound : ∀ z ∈ Metric.closedBall (0 : ℂ) R,
      ‖ZeroFree.Q E B z‖ ≤ Real.exp (R * B.card * q) := by
    intro z hz
    apply (ZeroFree.norm_Q_le E B hE z).trans
    apply Real.exp_le_exp.mpr
    have hz' : ‖z‖ ≤ R := by simpa using hz
    nlinarith [mul_nonneg (Nat.cast_nonneg B.card : (0 : ℝ) ≤ B.card) hq]
  refine ⟨L, hzero, hLd, hLe, ?_, ?_, ?_⟩
  · intro p hp
    exact coefficient_bound_of_analytic_log hR hLd hzero hLe hQbound hp
  · intro s
    exact truncation_bound_of_analytic_log hR hLd hzero hLe hQbound s
  · intro z hz
    exact half_disk_bound_of_analytic_log hR hLd hzero hLe hQbound hz


end Coeff
end Paper08
