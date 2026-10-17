import CalibrationDistance.Cumulative
import Mathlib.Tactic

open MeasureTheory ProbabilityTheory Real
open scoped BigOperators

namespace CalibrationDistance.Protocol

noncomputable section

/-- Bounded observables have an integrable square under any finite measure. -/
lemma integrable_sq_of_bounded_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ ω, |f ω| ≤ B) : Integrable (fun ω => f ω ^ 2) μ := by
  apply integrable_of_bounded_measurable (hf.pow_const 2) (B := B ^ 2)
  intro ω
  simpa only [sq_abs, abs_sq] using pow_le_pow_left₀ (abs_nonneg (f ω)) (hb ω) 2

/-- A bounded additive increment remains integrable at every fixed public history. -/
lemma integrable_increment (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B : ℝ}
    (hb : ∀ n h, |d n h| ≤ B) (n : ℕ) (h : History n) :
    Integrable (fun r : Round => d n (h,r)) (transition K A n h) := by
  exact integrable_of_bounded_measurable ((hd n).comp measurable_prodMk_left)
    (fun r => hb n (h,r))

/-- One step of the expectation recursion under the actual simultaneous-play law. -/
theorem integral_cumulative_succ (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B : ℝ}
    (hb : ∀ n h, |d n h| ≤ B) (n : ℕ) :
    (∫ h, cumulative d (n+1) h ∂law K A (n+1)) =
      (∫ h, cumulative d n h ∂law K A n) +
      ∫ h, ∫ r : Round, d n (h,r) ∂transition K A n h ∂law K A n := by
  have hi := integrable_cumulative K A d hd hb (n+1)
  have hi' : Integrable (fun z : History n × Round => cumulative d n z.1 + d n z)
      ((law K A n).compProd (transition K A n)) := hi
  haveI : IsProbabilityMeasure ((law K A n).compProd (transition K A n)) :=
    law_probability K A (n+1)
  have hdi : Integrable (d n) ((law K A n).compProd (transition K A n)) :=
    integrable_of_bounded_measurable (hd n) (hb n)
  change (∫ z : History n × Round, cumulative d n z.1 + d n z
    ∂(law K A n).compProd (transition K A n)) = _
  rw [Measure.integral_compProd hi']
  have heq : (fun h : History n => ∫ r : Round,
      cumulative d n h + d n (h,r) ∂transition K A n h) =
      (fun h : History n => cumulative d n h +
        ∫ r : Round, d n (h,r) ∂transition K A n h) := by
    funext h
    rw [integral_add (integrable_const _) (integrable_increment K A d hd hb n h)]
    simp
  rw [heq]
  have hei : Integrable (fun h => ∫ r : Round, d n (h,r) ∂transition K A n h) (law K A n) := by
    simpa using hdi.integral_compProd
  exact integral_add (integrable_cumulative K A d hd hb n) hei

/-- Expected cumulative increments are the sum of their actual conditional-law integrals. -/
theorem integral_cumulative_eq_sum (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B : ℝ}
    (hb : ∀ n h, |d n h| ≤ B) :
    ∀ n, (∫ h, cumulative d n h ∂law K A n) =
      ∑ i ∈ Finset.range n,
        ∫ h, ∫ r : Round, d i (h,r) ∂transition K A i h ∂law K A i
  | 0 => by simp [cumulative]
  | n+1 => by
    rw [integral_cumulative_succ K A d hd hb n, integral_cumulative_eq_sum K A d hd hb n,
      Finset.sum_range_succ]

/-- The mixed term vanishes because the current increment has mean zero at each history. -/
theorem integral_cumulative_sq_succ (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B : ℝ}
    (hb : ∀ n h, |d n h| ≤ B)
    (hcenter : ∀ n (h : History n), ∫ r : Round, d n (h,r) ∂transition K A n h = 0)
    (n : ℕ) :
    (∫ h, cumulative d (n+1) h ^ 2 ∂law K A (n+1)) =
      (∫ h, cumulative d n h ^ 2 ∂law K A n) +
      ∫ h, ∫ r : Round, d n (h,r) ^ 2 ∂transition K A n h ∂law K A n := by
  have hi := integrable_sq_of_bounded_measurable
    (μ := law K A (n+1)) (measurable_cumulative d hd (n+1)) (cumulative_abs_le d hb (n+1))
  have hi' : Integrable (fun z : History n × Round => (cumulative d n z.1 + d n z)^2)
      ((law K A n).compProd (transition K A n)) := hi
  have hs : Integrable (fun h => cumulative d n h ^ 2) (law K A n) :=
    integrable_sq_of_bounded_measurable (measurable_cumulative d hd n) (cumulative_abs_le d hb n)
  haveI : IsProbabilityMeasure ((law K A n).compProd (transition K A n)) :=
    law_probability K A (n+1)
  have hds : Integrable (fun z => d n z ^ 2)
      ((law K A n).compProd (transition K A n)) :=
    integrable_sq_of_bounded_measurable (hd n) (hb n)
  change (∫ z : History n × Round, (cumulative d n z.1 + d n z)^2
    ∂(law K A n).compProd (transition K A n)) = _
  rw [Measure.integral_compProd hi']
  have heq : (fun h : History n => ∫ r : Round,
      (cumulative d n h + d n (h,r))^2 ∂transition K A n h) =
      (fun h : History n => cumulative d n h ^ 2 +
        ∫ r : Round, d n (h,r)^2 ∂transition K A n h) := by
    funext h
    have hdi := integrable_increment K A d hd hb n h
    have hd2 : Integrable (fun r : Round => d n (h,r)^2) (transition K A n h) :=
      integrable_sq_of_bounded_measurable ((hd n).comp measurable_prodMk_left)
        (fun r => hb n (h,r))
    calc
      _ = ∫ r : Round, (cumulative d n h)^2 +
          (2 * cumulative d n h) * d n (h,r) + d n (h,r)^2 ∂transition K A n h := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun r => by ring)
      _ = (cumulative d n h)^2 + ∫ r : Round, d n (h,r)^2 ∂transition K A n h := by
        have hc : Integrable (fun _r : Round => cumulative d n h ^ 2) (transition K A n h) :=
          integrable_const _
        have hl : Integrable (fun r : Round => (2 * cumulative d n h) * d n (h,r))
            (transition K A n h) := hdi.const_mul _
        have hadd2 := integral_add (hc.add hl) hd2
        have hadd1 := integral_add hc hl
        simp only [Pi.add_apply] at hadd2 hadd1
        rw [hadd2, hadd1, integral_const_mul, hcenter n h]
        simp
  rw [heq]
  have hei : Integrable (fun h => ∫ r : Round, d n (h,r)^2 ∂transition K A n h) (law K A n) := by
    simpa using hds.integral_compProd
  exact integral_add hs hei

/-- Martingale orthogonality, derived from the actual centered transition kernels. -/
theorem integral_cumulative_sq_eq_sum (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B : ℝ}
    (hb : ∀ n h, |d n h| ≤ B)
    (hcenter : ∀ n (h : History n), ∫ r : Round, d n (h,r) ∂transition K A n h = 0) :
    ∀ n, (∫ h, cumulative d n h ^ 2 ∂law K A n) =
      ∑ i ∈ Finset.range n,
        ∫ h, ∫ r : Round, d i (h,r) ^ 2 ∂transition K A i h ∂law K A i
  | 0 => by simp [cumulative]
  | n+1 => by
    rw [integral_cumulative_sq_succ K A d hd hb hcenter n,
      integral_cumulative_sq_eq_sum K A d hd hb hcenter n, Finset.sum_range_succ]

end
end CalibrationDistance.Protocol
