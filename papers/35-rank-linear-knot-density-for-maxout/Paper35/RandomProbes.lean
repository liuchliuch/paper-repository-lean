import Paper35.RandomCount
import Paper35.Covariance
import Paper35.Deep
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Corollary 2.7: random probes and arbitrarily coupled parallel units

The random-path law and actual candidate law are sampled with their product,
expressing the source independence assumption. Each parallel unit has exactly
its specified iid marginal law; the joint law of different units is arbitrary.
All count measurability needed for Tonelli follows from the genuine continuous
path count graph proved in `RandomCount`. The only internal main-theorem input
is `WeightedCovarianceClaim`.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Paper35.RandomProbes
open Source Source.WeightedModel VisibleCrossing RandomCount

variable {d : ℕ}

/-- The actual covariance quadratic form of the original weight law, evaluated
on a direction, without introducing a separately postulated covariance matrix. -/
def originalProjectedVariance (m : WeightedModel d) (u : Space d) : ℝ :=
  variance (fun w => inner ℝ u w) m.weights

lemma measurable_originalProjectedVariance (m : WeightedModel d) :
    Measurable (originalProjectedVariance m) := by
  haveI := m.probability
  have hmean : Measurable (fun u : Space d => ∫ w, inner ℝ u w ∂m.weights) :=
    ((measurable_fst.inner measurable_snd).stronglyMeasurable.integral_prod_right'
      (ν := m.weights)).measurable
  have hvar : Measurable (fun u : Space d => ∫ w,
      (inner ℝ u w - ∫ w', inner ℝ u w' ∂m.weights)^2 ∂m.weights) :=
    (((measurable_fst.inner measurable_snd).sub (hmean.comp measurable_fst)).pow_const 2).stronglyMeasurable.integral_prod_right'.measurable
  convert hvar using 1
  funext u
  exact variance_eq_integral (by fun_prop)

lemma projectedVariance_eq_original_of_constant (m : WeightedModel d) (B : ℝ≥0)
    (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B) (u : Space d) :
    m.projectedVariance u = originalProjectedVariance m u := by
  rw [projectedVariance_eq_variance, tilted_eq_weights_of_constant m B hb]
  rfl

def covarianceSpeed (m : WeightedModel d) (p : Probe d) (s : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.sqrt (originalProjectedVariance m (deriv p.curve s)))

lemma measurable_covarianceSpeed (m : WeightedModel d) (p : Probe d) :
    Measurable (covarianceSpeed m p) :=
  (((measurable_originalProjectedVariance m).comp (measurable_deriv p.curve)).sqrt).ennreal_ofReal

/-- Constant-envelope specialization of the already-proved internal covariance
theorem. In particular the variance here is for the original weight law. -/
theorem constantEnvelope_count_bound (hcov : WeightedCovarianceClaim (d := d))
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hW : MemLp (fun w => w) 2 m.weights) (K : ℕ) (hK : 2 ≤ K) (p : Probe d) :
    m.expectedCount K p ≤ ((K : ℝ≥0∞) * B / ENNReal.ofReal (Real.sqrt 3)) *
      ∫⁻ s in Icc 0 p.length, covarianceSpeed m p s := by
  have ht : MemLp (fun w => w) 2 m.tilted := by
    rw [tilted_eq_weights_of_constant m B hb]
    exact hW
  have H := hcov m ht K hK p
  rw [average_eq_of_constant m B hb] at H
  simpa only [projectedVariance_eq_original_of_constant m B hb, covarianceSpeed] using H

/-- Exact independence/Tonelli identity for the actual random count. -/
theorem randomProbe_expectedCount_eq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [SFinite μ] (m : WeightedModel d) (K : ℕ)
    (p : Ω → Probe d) (hL : Measurable (fun ω => (p ω).length))
    (hγ : Measurable (fun z : RandomProbeDomain p => (p z.1.1).curve z.1.2))
    (hLN : LusinNovikovInput (CodeParameter d K) ℝ) :
    (∫⁻ z : Ω × (Fin K → Candidate d),
      switchCount (scores (p z.1) z.2) (p z.1).length ∂μ.prod (m.iid K)) =
      ∫⁻ ω, m.expectedCount K (p ω) ∂μ := by
  exact lintegral_prod _ (measurable_randomProbeSwitchCount p hL hγ hLN).aemeasurable

/-- Equation (2.14) under exactly the random-probe representation and
independence assumptions. The inequality is extended-valued, so it also
contains the source's finite-expectation case. -/
theorem randomProbe_covariance_bound {Ω : Type*} [MeasurableSpace Ω]
    (hcov : WeightedCovarianceClaim (d := d)) (μ : Measure Ω) [SFinite μ]
    (m : WeightedModel d) (B : ℝ≥0) (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B)
    (hW : MemLp (fun w => w) 2 m.weights) (K : ℕ) (hK : 2 ≤ K)
    (p : Ω → Probe d) (hL : Measurable (fun ω => (p ω).length))
    (hγ : Measurable (fun z : RandomProbeDomain p => (p z.1.1).curve z.1.2))
    (hLN : LusinNovikovInput (CodeParameter d K) ℝ) :
    (∫⁻ z : Ω × (Fin K → Candidate d),
      switchCount (scores (p z.1) z.2) (p z.1).length ∂μ.prod (m.iid K)) ≤
      ((K : ℝ≥0∞) * B / ENNReal.ofReal (Real.sqrt 3)) *
        ∫⁻ ω, (∫⁻ s in Icc 0 (p ω).length, covarianceSpeed m (p ω) s) ∂μ := by
  rw [randomProbe_expectedCount_eq μ m K p hL hγ hLN]
  calc
    _ ≤ ∫⁻ ω, ((K : ℝ≥0∞) * B / ENNReal.ofReal (Real.sqrt 3)) *
        (∫⁻ s in Icc 0 (p ω).length, covarianceSpeed m (p ω) s) ∂μ :=
      lintegral_mono (fun ω => constantEnvelope_count_bound hcov m B hb hW K hK (p ω))
    _ = _ := lintegral_const_mul' _ _ (ENNReal.div_ne_top
      (ENNReal.mul_ne_top (by simp) ENNReal.coe_ne_top)
      (ENNReal.ofReal_pos.mpr (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))).ne')

/-- Exact marginal-law transport of a true count, also valid for singular
parameter maps. -/
theorem expectedCount_eq_of_marginal {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : WeightedModel d) (K : ℕ) (p : Probe d)
    (a : Ω → Fin K → Candidate d) (ha : Measurable a)
    (hlaw : μ.map a = m.iid K) (hLN : LusinNovikovInput (CodeParameter d K) ℝ) :
    expectedSwitchCount μ (fun ω => scores p (a ω)) p.length = m.expectedCount K p := by
  have hc := measurable_affineSwitchCount p.curve p.length p.length_pos p.lipschitz.continuousOn hLN
  have H := lintegral_map hc ha (μ := μ)
  rw [hlaw] at H
  exact H.symm

/-- Equation (2.15), with arbitrary coupling across units and only the stated
iid marginal within each unit. The left side counts the union of actual
parameter switches, so coincident component changes are counted once. -/
theorem parallel_covariance_bound {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    (hcov : WeightedCovarianceClaim (d := d)) (μ : Measure Ω)
    (K : ι → ℕ) (m : ι → WeightedModel d) (B : ι → ℝ≥0)
    (hb : ∀ r, ∀ᵐ w ∂(m r).weights, (m r).b₀ w = B r)
    (hW : ∀ r, MemLp (fun w => w) 2 (m r).weights) (hK : ∀ r, 2 ≤ K r)
    (p : Probe d) (a : (r : ι) → Ω → Fin (K r) → Candidate d)
    (ha : ∀ r, Measurable (a r)) (hlaw : ∀ r, μ.map (a r) = (m r).iid (K r))
    (hLN : ∀ r, LusinNovikovInput (CodeParameter d (K r)) ℝ) :
    (∫⁻ ω, Deep.jointSwitchCount K (fun r => scores p (a r ω)) p.length ∂μ) ≤
      (1 / ENNReal.ofReal (Real.sqrt 3)) * ∫⁻ s in Icc 0 p.length,
        ∑ r, (K r : ℝ≥0∞) * B r * covarianceSpeed (m r) p s := by
  classical
  have hc (r : ι) : Measurable (fun ω => switchCount (scores p (a r ω)) p.length) :=
    (measurable_affineSwitchCount p.curve p.length p.length_pos p.lipschitz.continuousOn (hLN r)).comp (ha r)
  calc
    _ ≤ ∑ r, expectedSwitchCount μ (fun ω => scores p (a r ω)) p.length :=
      Deep.expected_jointSwitchCount_le μ K (fun ω r => scores p (a r ω)) p.length hc
    _ = ∑ r, (m r).expectedCount (K r) p := by
      apply Finset.sum_congr rfl
      intro r _
      exact expectedCount_eq_of_marginal μ (m r) (K r) p (a r) (ha r) (hlaw r) (hLN r)
    _ ≤ ∑ r, ((K r : ℝ≥0∞) * B r / ENNReal.ofReal (Real.sqrt 3)) *
        ∫⁻ s in Icc 0 p.length, covarianceSpeed (m r) p s :=
      Finset.sum_le_sum (fun r _ => constantEnvelope_count_bound hcov (m r) (B r) (hb r) (hW r) (K r) (hK r) p)
    _ = (1 / ENNReal.ofReal (Real.sqrt 3)) * ∑ r, ((K r : ℝ≥0∞) * B r) *
        ∫⁻ s in Icc 0 p.length, covarianceSpeed (m r) p s := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _
      simp only [div_eq_mul_inv, one_mul]
      ac_rfl
    _ = _ := by
      congr 1
      rw [lintegral_finset_sum _ (fun r _ => (measurable_covarianceSpeed (m r) p).const_mul _)]
      apply Finset.sum_congr rfl
      intro r _
      exact (lintegral_const_mul _ (measurable_covarianceSpeed (m r) p)).symm

end Paper35.RandomProbes
