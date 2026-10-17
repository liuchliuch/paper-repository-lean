import CalibrationDistance.Protocol
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Bounded additive processes under the actual nested public-history law.
The proofs use the finite composition-product recursion directly. No change
of the forecasting strategy class or extra independence assumption occurs. -/

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace CalibrationDistance.Protocol

noncomputable section

def cumulative (d : (n : ℕ) → History (n + 1) → ℝ) :
    (n : ℕ) → History n → ℝ
  | 0, _ => 0
  | n+1, h => cumulative d n h.1 + d n h

theorem measurable_cumulative (d : (n : ℕ) → History (n + 1) → ℝ)
    (hd : ∀ n, Measurable (d n)) : ∀ n, Measurable (cumulative d n)
  | 0 => measurable_const
  | n+1 => (measurable_cumulative d hd n |>.comp measurable_fst).add (hd n)

theorem cumulative_abs_le (d : (n : ℕ) → History (n + 1) → ℝ) {B : ℝ}
    (hd : ∀ n h, |d n h| ≤ B) : ∀ n h, |cumulative d n h| ≤ (n : ℝ) * B
  | 0, _ => by simp [cumulative]
  | n+1, h => by
    change |cumulative d n h.1 + d n h| ≤ _
    calc
      _ ≤ |cumulative d n h.1| + |d n h| := abs_add_le _ _
      _ ≤ (n : ℝ) * B + B := add_le_add (cumulative_abs_le d hd n h.1) (hd n h)
      _ = ((n+1 : ℕ) : ℝ) * B := by push_cast; ring

lemma integrable_of_bounded_measurable {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ ω, |f ω| ≤ B) : Integrable f μ := by
  apply (integrable_const B).mono' hf.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hb ω

lemma integrable_exp_of_bounded {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    {B : ℝ} (hb : ∀ ω, |f ω| ≤ B) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * f ω)) μ := by
  apply integrable_of_bounded_measurable ((measurable_const.mul hf).exp)
    (B := Real.exp (|t| * B))
  intro ω
  rw [abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t * f ω ≤ |t * f ω| := le_abs_self _
    _ = |t| * |f ω| := abs_mul _ _
    _ ≤ |t| * B := mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg _)

theorem integrable_cumulative (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B : ℝ}
    (hb : ∀ n h, |d n h| ≤ B) (n : ℕ) :
    Integrable (cumulative d n) (law K A n) :=
  integrable_of_bounded_measurable (measurable_cumulative d hd n)
    (cumulative_abs_le d hb n)

/-- Iteration of the conditional exponential bound under simultaneous transitions. -/
theorem cumulative_mgf_le (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B c : ℝ}
    (hb : ∀ n h, |d n h| ≤ B)
    (hm : ∀ n (h : History n) t,
      (∫ r : Round, Real.exp (t * d n (h,r)) ∂transition K A n h) ≤
        Real.exp (c * t ^ 2 / 2)) :
    ∀ n t, (∫ h, Real.exp (t * cumulative d n h) ∂law K A n) ≤
      Real.exp ((n : ℝ) * c * t ^ 2 / 2)
  | 0, t => by simp [law, cumulative]
  | n+1, t => by
    have hi := integrable_exp_of_bounded (μ := law K A (n+1))
      (measurable_cumulative d hd (n+1)) (cumulative_abs_le d hb (n+1)) t
    have hp := integrable_exp_of_bounded (μ := law K A n)
      (measurable_cumulative d hd n) (cumulative_abs_le d hb n) t
    change (∫ h : History n × Round,
      Real.exp (t * (cumulative d n h.1 + d n h))
      ∂(law K A n).compProd (transition K A n)) ≤ _
    have hi' : Integrable (fun h : History n × Round =>
        Real.exp (t * (cumulative d n h.1 + d n h)))
        ((law K A n).compProd (transition K A n)) := hi
    rw [Measure.integral_compProd hi']
    calc
      _ = ∫ h, Real.exp (t * cumulative d n h) *
          (∫ r : Round, Real.exp (t * d n (h,r)) ∂transition K A n h) ∂law K A n := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun h => by
          simp only [cumulative, mul_add, Real.exp_add, integral_const_mul]
      _ ≤ ∫ h, Real.exp (t * cumulative d n h) * Real.exp (c * t ^ 2 / 2) ∂law K A n := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall fun h => mul_nonneg (by positivity)
            (integral_nonneg fun _ => (Real.exp_pos _).le)
        · exact hp.mul_const _
        · exact Filter.Eventually.of_forall fun h =>
            mul_le_mul_of_nonneg_left (hm n h t) (Real.exp_pos _).le
      _ = (∫ h, Real.exp (t * cumulative d n h) ∂law K A n) *
          Real.exp (c * t ^ 2 / 2) := integral_mul_const _ _
      _ ≤ Real.exp ((n : ℝ) * c * t ^ 2 / 2) * Real.exp (c * t ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right (cumulative_mgf_le K A d hd hb hm n t) (Real.exp_pos _).le
      _ = Real.exp (((n+1 : ℕ) : ℝ) * c * t ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        ring

/-- The full cumulative residual has the exact sub-Gaussian parameter used in
Appendix A once the one-round product-distribution bound is supplied. -/
theorem cumulative_hasSubgaussianMGF (K : BehavioralForecaster) (A : RandomizedAdversary)
    (d : (n : ℕ) → History (n + 1) → ℝ) (hd : ∀ n, Measurable (d n)) {B : ℝ}
    (hb : ∀ n h, |d n h| ≤ B) (c : ℝ≥0)
    (hm : ∀ n (h : History n) t,
      (∫ r : Round, Real.exp (t * d n (h,r)) ∂transition K A n h) ≤
        Real.exp ((c : ℝ) * t ^ 2 / 2)) (n : ℕ) :
    HasSubgaussianMGF (cumulative d n) ((n : ℝ≥0) * c) (law K A n) := by
  constructor
  · exact fun t => integrable_exp_of_bounded (measurable_cumulative d hd n)
      (cumulative_abs_le d hb n) t
  · intro t
    simpa using cumulative_mgf_le K A d hd hb hm n t

end
end CalibrationDistance.Protocol
