import Paper38.Rates
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Probability assembly used in Section 7

These are integration and rate lemmas only. They do not assume the paper's
particle convergence as an input and do not assert the missing Gaussian
matching, covariance-concentration or log-Wishart estimates.
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Paper38.ProbabilityAssembly

/-- Cauchy--Schwarz on a measurable exceptional event. This is the genuine
measure integral used in the final step of Lemma 7.2. -/
theorem exceptional_event_cauchy_schwarz {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (bad : Set Ω) (hbad : MeasurableSet bad)
    (Z : Ω → ℝ≥0∞) (hZ : Measurable Z) :
    (∫⁻ ω in bad, Z ω ∂P) ≤
      (P bad) ^ (1 / 2 : ℝ) * (∫⁻ ω, Z ω ^ 2 ∂P) ^ (1 / 2 : ℝ) := by
  let I : Ω → ℝ≥0∞ := bad.indicator (fun _ => 1)
  have hI : Measurable I := measurable_const.indicator hbad
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq P
    (show (2 : ℝ).HolderConjugate 2 by norm_num [Real.holderConjugate_iff])
    hI.aemeasurable hZ.aemeasurable
  have hIpow : (fun ω => I ω ^ (2 : ℝ)) = I := by
    funext ω
    by_cases h : ω ∈ bad <;> simp [I, h]
  have hprod : I * Z = bad.indicator Z := by
    funext ω
    by_cases h : ω ∈ bad <;> simp [I, h]
  rw [hIpow, hprod, lintegral_indicator hbad] at hholder
  simpa only [I, lintegral_indicator hbad, lintegral_one, Measure.restrict_apply_univ, ENNReal.rpow_two] using hholder

/-- A pathwise envelope may be inserted before the exceptional-event
Cauchy--Schwarz bound. The envelope's second moment is a separate prerequisite. -/
theorem exceptional_event_envelope {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (bad : Set Ω) (hbad : MeasurableSet bad)
    (f Z : Ω → ℝ≥0∞) (hZ : Measurable Z) (C : ℝ≥0∞)
    (henvelope : ∀ ω ∈ bad, f ω ≤ C * Z ω) :
    (∫⁻ ω in bad, f ω ∂P) ≤
      C * ((P bad) ^ (1 / 2 : ℝ) * (∫⁻ ω, Z ω ^ 2 ∂P) ^ (1 / 2 : ℝ)) := by
  calc
    (∫⁻ ω in bad, f ω ∂P) ≤ ∫⁻ ω in bad, C * Z ω ∂P := by
      apply lintegral_mono_ae
      filter_upwards [ae_restrict_mem hbad] with ω hω
      exact henvelope ω hω
    _ = C * ∫⁻ ω in bad, Z ω ∂P := lintegral_const_mul C hZ
    _ ≤ _ := mul_le_mul_left' (exceptional_event_cauchy_schwarz P bad hbad Z hZ) C

/-- The exponentially rare complement does not change any source N-rate;
the constant is independent of the sample size. -/
theorem exponential_le_rate (d N : ℕ) (hd : 1 ≤ d) (hN : 1 ≤ N)
    (c : ℝ) (hc : 0 < c) : Real.exp (-c * N) ≤ c⁻¹ * Model.rate d N := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hx : 0 < c * N := mul_pos hc hNr
  have he : c * N ≤ Real.exp (c * N) := by
    have := Real.add_one_le_exp (c * N)
    linarith
  have hi : (Real.exp (c * N))⁻¹ ≤ (c * N)⁻¹ := inv_anti₀ hx he
  calc
    Real.exp (-c * N) = (Real.exp (c * N))⁻¹ := by rw [← Real.exp_neg]; congr 1; ring
    _ ≤ (c * N)⁻¹ := hi
    _ = c⁻¹ * (N : ℝ)⁻¹ := mul_inv _ _
    _ ≤ c⁻¹ * Model.rate d N :=
      mul_le_mul_of_nonneg_left (Model.inv_sampleSize_le_rate d N hd hN) (inv_nonneg.mpr hc.le)

end Paper38.ProbabilityAssembly
