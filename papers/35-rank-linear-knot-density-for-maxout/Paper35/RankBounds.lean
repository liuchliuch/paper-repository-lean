import Paper35.Rank
import Mathlib.Probability.CDF
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Paper35.RankBounds

def φ (b : ℝ) : ℝ := gaussianPDFReal 0 1 b
def Φ (b : ℝ) : ℝ := cdf (gaussianReal 0 1) b

def maxLaw (n : ℕ) : Measure ℝ := standardNormalSequence.map (prefixMax n)
instance maxLaw_probability (n : ℕ) : IsProbabilityMeasure (maxLaw n) := by
  apply Measure.isProbabilityMeasure_map
  exact (continuous_prefixMax n).measurable.aemeasurable

lemma maxLaw_cdf (n : ℕ) (t : ℝ) : cdf (maxLaw n) t = Φ t ^ (n+1) := by
  rw [cdf_eq_real, measureReal_def, maxLaw,
    Measure.map_apply (continuous_prefixMax n).measurable measurableSet_Iic]
  change (standardNormalSequence {x | prefixMax n x ≤ t}).toReal = _
  rw [prefixMax_distribution, ENNReal.toReal_pow]
  rw [Φ, cdf_eq_real, measureReal_def]

/-- Standard signed tail integration for an arbitrary integrable real law,
obtained from the two layer-cake identities and Tonelli (Folland, Real
Analysis, 2nd ed., Theorem 2.37; Durrett, Probability: Theory and Examples,
5th ed., integration/tail formulas). No Gaussian or Maxout is mentioned. -/
def TailIntegrationInput : Prop :=
  ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν], Integrable (id : ℝ → ℝ) ν → ∀ b : ℝ,
    IntegrableOn (fun t => 1-cdf ν t) (Ioi b) volume ∧
    IntegrableOn (cdf ν) (Iic b) volume ∧
    (∫ x, x ∂ν) = b + (∫ t in Ioi b, 1-cdf ν t) - ∫ t in Iic b, cdf ν t

/-- The standard normal first truncated moment / stop-loss identity. It is a
classical one-variable Gaussian integration-by-parts input; its statement is
only about one N(0,1) variable, not a maximum or a switching coefficient. -/
def GaussianStopLossInput : Prop :=
  ∀ b : ℝ, (∫ x, max (x-b) 0 ∂gaussianReal 0 1) = φ b - b*(1-Φ b)

/-- Tangent inequality for the log-concave standard Gaussian CDF, in its
power/exponential form. Classical source: Bagnoli--Bergstrom, Economic Theory
26 (2005), Theorem 1 (normal density/CDF log-concavity), followed by the
supporting-line inequality for a differentiable concave function. -/
def GaussianCDFTangentInput : Prop :=
  ∀ (K : ℕ) (b t : ℝ), 0 < Φ b → t ≤ b →
    Φ t ^ K ≤ Φ b ^ K * Real.exp ((K : ℝ)*φ b/Φ b*(t-b))

lemma phi_pos (b : ℝ) : 0 < φ b := gaussianPDFReal_pos 0 1 b one_ne_zero

lemma prefixMax_stopLoss_bound (n : ℕ) (x : ℕ → ℝ) (b : ℝ) :
    prefixMax n x ≤ b + ∑ j ∈ Finset.range (n+1), max (x j-b) 0 := by
  induction n with
  | zero =>
    simp only [prefixMax, Nat.zero_add, Finset.sum_range_one]
    linarith [le_max_left (x 0-b) 0]
  | succ n ih =>
    rw [prefixMax, Finset.sum_range_succ]
    apply max_le
    · exact ih.trans (by linarith [le_max_right (x (n+1)-b) 0])
    · have hsum : 0 ≤ ∑ j ∈ Finset.range (n+1), max (x j-b) 0 :=
        Finset.sum_nonneg (fun _ _ => le_max_right _ _)
      linarith [le_max_left (x (n+1)-b) 0]

lemma integrable_stopLoss_coordinate (b : ℝ) (j : ℕ) :
    Integrable (fun x : ℕ → ℝ => max (x j-b) 0) standardNormalSequence :=
  ((integrable_normalCoordinate j).sub (integrable_const b)).sup (integrable_const 0)

lemma stopLoss_coordinate (hstop : GaussianStopLossInput) (b : ℝ) (j : ℕ) :
    (∫ x : ℕ → ℝ, max (x j-b) 0 ∂standardNormalSequence) = φ b-b*(1-Φ b) := by
  have H := integral_map (μ := standardNormalSequence) (φ := fun x : ℕ → ℝ => x j)
    (f := fun y : ℝ => max (y-b) 0) (measurable_pi_apply j).aemeasurable (by fun_prop)
  rw [normalCoordinate_law] at H
  rw [← H, hstop]

/-- The upper half of (7.1), with b specified by its exact quantile equation. -/
theorem gaussianMaxMean_quantile_upper (hstop : GaussianStopLossInput)
    {K : ℕ} (hK : 2 ≤ K) (b : ℝ) (hb : Φ b = 1-1/(K : ℝ)) :
    gaussianMaxMean K ≤ (K : ℝ)*φ b := by
  obtain ⟨n, rfl⟩ : ∃ n, K=n+1 := ⟨K-1, by omega⟩
  have hbound : gaussianMaxMean (n+1) ≤
      b + ∫ x : ℕ → ℝ, ∑ j ∈ Finset.range (n+1), max (x j-b) 0 ∂standardNormalSequence := by
    change (∫ x, prefixMax n x ∂standardNormalSequence) ≤ _
    have H := integral_mono (integrable_prefixMax n)
      ((integrable_const b).add (integrable_finset_sum _ (fun j _ => integrable_stopLoss_coordinate b j)))
      (fun x => prefixMax_stopLoss_bound n x b)
    change (∫ x, prefixMax n x ∂standardNormalSequence) ≤
      ∫ x : ℕ → ℝ, b + ∑ j ∈ Finset.range (n+1), max (x j-b) 0 ∂standardNormalSequence at H
    rw [integral_add (integrable_const b)
      (integrable_finset_sum _ (fun j _ => integrable_stopLoss_coordinate b j))] at H
    simpa only [integral_const, measureReal_univ_eq_one, one_smul] using H
  rw [integral_finset_sum _ (fun j _ => integrable_stopLoss_coordinate b j)] at hbound
  simp_rw [stopLoss_coordinate hstop b] at hbound
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hbound
  rw [hb] at hbound
  have hn : (n+1 : ℝ) ≠ 0 := by positivity
  have heq : b+(n+1 : ℝ)*(φ b-b*(1-(1-1/(n+1 : ℝ)))) = (n+1 : ℝ)*φ b := by
    field_simp
    <;> ring
  simpa only [Nat.cast_add, Nat.cast_one, heq] using hbound

lemma gaussianMaxMean_tail (htail : TailIntegrationInput) (n : ℕ) (b : ℝ) :
    IntegrableOn (fun t => Φ t^(n+1)) (Iic b) volume ∧
    gaussianMaxMean (n+1) = b + (∫ t in Ioi b, 1-Φ t^(n+1)) - ∫ t in Iic b, Φ t^(n+1) := by
  have hi : Integrable (id : ℝ → ℝ) (maxLaw n) :=
    (integrable_map_measure measurable_id.aestronglyMeasurable
      (continuous_prefixMax n).measurable.aemeasurable).2 (integrable_prefixMax n)
  obtain ⟨hp, hn, heq⟩ := htail (maxLaw n) hi b
  have hmean : (∫ x, x ∂maxLaw n) = gaussianMaxMean (n+1) := by
    exact integral_map (μ := standardNormalSequence) (φ := prefixMax n)
      (f := fun x : ℝ => x) (continuous_prefixMax n).measurable.aemeasurable
      measurable_id.aestronglyMeasurable
  have hn' : IntegrableOn (fun t => Φ t^(n+1)) (Iic b) volume := by
    convert hn using 1
    ext t
    exact (maxLaw_cdf n t).symm
  refine ⟨hn', ?_⟩
  rw [hmean] at heq
  simpa only [maxLaw_cdf] using heq

lemma integral_tangent_exp {r : ℝ} (hr : 0 < r) (b q : ℝ) (K : ℕ) :
    IntegrableOn (fun t => q^K*Real.exp (r*(t-b))) (Iic b) volume ∧
    (∫ t in Iic b, q^K*Real.exp (r*(t-b))) = q^K/r := by
  have heq : (fun t : ℝ => q^K*Real.exp (r*(t-b))) =
      (fun t => (q^K*Real.exp (-r*b))*Real.exp (r*t)) := by
    funext t
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [heq]
  refine ⟨(integrableOn_exp_mul_Iic hr b).const_mul _, ?_⟩
  rw [integral_const_mul, integral_exp_mul_Iic hr]
  have hcancel : Real.exp (-r*b)*Real.exp (r*b) = 1 := by
    rw [← Real.exp_add]
    convert Real.exp_zero using 1
    ring
  calc
    _ = q^K*(Real.exp (-r*b)*Real.exp (r*b))/r := by ring
    _ = _ := by rw [hcancel, mul_one]

/-- The lower half of (7.1). Its estimation, exponential integral and
quantile cancellation are actual proofs; inputs are only generic tail
integration and the classical log-CDF tangent inequality. -/
theorem gaussianMaxMean_quantile_lower (htail : TailIntegrationInput)
    (htangent : GaussianCDFTangentInput) {K : ℕ} (hK : 2 ≤ K)
    (b : ℝ) (hb : Φ b = 1-1/(K : ℝ)) :
    b-Φ b^(K+1)/((K : ℝ)*φ b) ≤ gaussianMaxMean K := by
  have hKr : (2 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hq : 0 < Φ b := by rw [hb]; exact sub_pos.mpr ((div_lt_one hKpos).mpr (by linarith))
  let r : ℝ := (K : ℝ)*φ b/Φ b
  have hr : 0 < r := div_pos (mul_pos hKpos (phi_pos b)) hq
  obtain ⟨n, hKn⟩ : ∃ n, K=n+1 := ⟨K-1, by omega⟩
  obtain ⟨hint, heq⟩ := gaussianMaxMean_tail htail n b
  rw [← hKn] at hint heq
  obtain ⟨hexpi, hexp⟩ := integral_tangent_exp hr b (Φ b) K
  have hneg : (∫ t in Iic b, Φ t^K) ≤ Φ b^K/r := by
    rw [← hexp]
    apply integral_mono_ae hint hexpi
    exact (ae_restrict_mem measurableSet_Iic).mono (fun t ht => htangent K b t hq ht)
  have hpos : 0 ≤ ∫ t in Ioi b, 1-Φ t^K := by
    apply integral_nonneg
    intro t
    exact sub_nonneg.mpr (pow_le_one₀ (cdf_nonneg _ _) (cdf_le_one _ _))
  have hratio : Φ b^K/r = Φ b^(K+1)/((K : ℝ)*φ b) := by
    dsimp [r]
    rw [pow_succ]
    field_simp
  rw [hratio] at hneg
  linarith

end Paper35.RankBounds
