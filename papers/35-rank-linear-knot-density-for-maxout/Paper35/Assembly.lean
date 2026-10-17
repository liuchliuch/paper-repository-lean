import Paper35.SourceModel
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Genuine-law foundations and conditional assembly for Theorem 2.3

The probability assertions below are consequences of the conditional-density
normalization and the actual envelope tilt. The final assembly theorem is
explicitly conditional on the two still separate analytic claims: the exact
visible-crossing identity and the weighted visibility estimate. In particular,
this file does not assert that either analytic claim has been established.
-/

noncomputable section
open MeasureTheory Set
open scoped ENNReal NNReal

namespace Paper35.Source.WeightedModel
variable {d : ℕ}

/-- The conditional score law really has mass one. -/
instance joint_isProbability (m : WeightedModel d) : IsProbabilityMeasure m.joint := by
  letI : IsProbabilityMeasure m.weights := m.probability
  constructor
  rw [joint, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_prod (fun θ => m.g θ.1 θ.2) m.measurable_g.aemeasurable]
  calc
    (∫⁻ w, ∫⁻ b, m.g w b ∂volume ∂m.weights) = ∫⁻ _w, (1 : ℝ≥0∞) ∂m.weights :=
      lintegral_congr_ae m.normalized_g
    _ = 1 := by simp

/-- Dividing the genuine envelope by its positive finite average gives a
probability law, without a moment hypothesis. -/
instance tilted_isProbability (m : WeightedModel d) : IsProbabilityMeasure m.tilted := by
  constructor
  rw [tilted, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const (f := fun w => (m.b₀ w : ℝ≥0∞)) _
    (measurable_coe_nnreal_ennreal.comp m.measurable_b₀)]
  exact ENNReal.mul_inv_cancel (ne_of_gt m.average_pos) m.average_finite.ne

/-- The specified finite product is an iid probability model. -/
instance iid_isProbability (m : WeightedModel d) (K : ℕ) :
    IsProbabilityMeasure (m.iid K) := by
  unfold iid
  infer_instance

/-- The CDF in the source crossing formula takes values in the unit interval. -/
theorem scoreCDF_le_one (m : WeightedModel d) (x : Space d) (y : ℝ) :
    m.scoreCDF x y ≤ 1 := by
  unfold scoreCDF
  calc
    _ ≤ m.joint univ := measure_mono (subset_univ _)
    _ = 1 := measure_univ

/-- A constant envelope has that same average, including almost everywhere
constant representatives. -/
theorem average_eq_of_constant (m : WeightedModel d) (B : ℝ≥0)
    (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B) : m.average = B := by
  letI : IsProbabilityMeasure m.weights := m.probability
  unfold average
  calc
    (∫⁻ w, (m.b₀ w : ℝ≥0∞) ∂m.weights) = ∫⁻ _w, (B : ℝ≥0∞) ∂m.weights := by
      apply lintegral_congr_ae
      filter_upwards [hb] with w hw
      rw [hw]
    _ = B := by simp

/-- The constant-envelope case recovers the original weight law (Remark 2.4). -/
theorem tilted_eq_weights_of_constant (m : WeightedModel d) (B : ℝ≥0)
    (hb : ∀ᵐ w ∂m.weights, m.b₀ w = B) : m.tilted = m.weights := by
  have hB := m.average_eq_of_constant B hb
  have hB0 : (B : ℝ≥0∞) ≠ 0 := by
    rw [← hB]
    exact ne_of_gt m.average_pos
  unfold tilted
  rw [hB]
  have hdensity : (fun w => (m.b₀ w : ℝ≥0∞) / B) =ᵐ[m.weights] (1 : Space d → ℝ≥0∞) := by
    filter_upwards [hb] with w hw
    simp only [hw, Pi.one_apply]
    exact ENNReal.div_self hB0 ENNReal.coe_ne_top
  rw [withDensity_congr_ae hdensity, withDensity_one]

/-- The choose-two identity before cancellation, valid directly in the
nonnegative extended reals. -/
theorem choose_two_mul_two (K : ℕ) :
    (K.choose 2 : ℝ≥0∞) * 2 = (K : ℝ≥0∞) * ((K - 1 : ℕ) : ℝ≥0∞) := by
  have hnat : K.choose 2 * 2 = K * (K - 1) := by
    have h := Nat.descFactorial_eq_factorial_mul_choose K 2
    simpa [Nat.descFactorial_succ, Nat.factorial_two, Nat.mul_comm] using h.symm
  exact_mod_cast hnat

/-- Pair counting and the visibility denominator cancel to a linear rank. -/
theorem choose_two_div_rank (K : ℕ) (hK : 2 ≤ K) :
    (K.choose 2 : ℝ≥0∞) / ((K - 1 : ℕ) : ℝ≥0∞) = (K : ℝ≥0∞) / 2 := by
  have hden : ((K - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show K - 1 ≠ 0 by omega)
  apply (ENNReal.div_eq_div_iff (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    ENNReal.ofNat_ne_top hden (ENNReal.natCast_ne_top _)).2
  simpa [mul_comm] using choose_two_mul_two K

/-- The rank cancellation retains arbitrary extended envelope mass. -/
theorem weighted_rank_cancellation (K : ℕ) (hK : 2 ≤ K) (B : ℝ≥0∞) :
    (K.choose 2 : ℝ≥0∞) * (B / ((K - 1 : ℕ) : ℝ≥0∞)) =
      (K : ℝ≥0∞) * B / 2 := by
  calc
    _ = ((K.choose 2 : ℝ≥0∞) / ((K - 1 : ℕ) : ℝ≥0∞)) * B := by
      simp only [div_eq_mul_inv]
      ac_rfl
    _ = ((K : ℝ≥0∞) / 2) * B := by rw [choose_two_div_rank K hK]
    _ = (K : ℝ≥0∞) * B / 2 := by
      simp only [div_eq_mul_inv]
      ac_rfl

/-- Integral assembly of (2.6) from the genuine exact-crossing identity (3.7)
and the isolated visibility bound (4.1). Both hypotheses are explicit proof
obligations; this is not an unconditional proof of Theorem 2.3. -/
theorem weightedVisibility_of_crossing_visibility
    (hcross : ExactCrossingClaim (d := d))
    (hvisibility : VisibilityLemmaClaim (d := d)) :
    WeightedVisibilityClaim (d := d) := by
  intro m K hK p
  have hindex : K - 2 + 1 = K - 1 := by omega
  have hden : ((K - 1 : ℕ) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show K - 1 ≠ 0 by omega)
  have hcoeff : m.average / ((K - 1 : ℕ) : ℝ≥0∞) ≠ ∞ :=
    ENNReal.div_ne_top m.average_finite.ne hden
  rw [hcross m K hK p]
  calc
    _ ≤ (K.choose 2 : ℝ≥0∞) * ∫⁻ s in Icc 0 p.length,
          (m.average / ((K - 1 : ℕ) : ℝ≥0∞)) * m.directionalGini (deriv p.curve s) := by
      apply mul_le_mul_left'
      apply lintegral_mono
      intro s
      simpa only [hindex] using hvisibility m (K - 2) (p.curve s) (deriv p.curve s)
    _ = (K.choose 2 : ℝ≥0∞) *
          ((m.average / ((K - 1 : ℕ) : ℝ≥0∞)) *
            ∫⁻ s in Icc 0 p.length, m.directionalGini (deriv p.curve s)) := by
      rw [lintegral_const_mul' _ _ hcoeff]
    _ = ((K : ℝ≥0∞) * m.average / 2) *
          ∫⁻ s in Icc 0 p.length, m.directionalGini (deriv p.curve s) := by
      rw [← mul_assoc, weighted_rank_cancellation K hK m.average]

end Paper35.Source.WeightedModel

namespace Paper35

/-- The elementary rank comparison behind the second inequality of (2.9). -/
theorem rank_le_twice_rank_sub_one (K : ℕ) (hK : 2 ≤ K) :
    (K : ℝ) ≤ 2 * ((K : ℝ) - 1) := by
  have hk : (2 : ℝ) ≤ K := by exact_mod_cast hK
  linarith

/-- The coefficient `2/sqrt(3)` is uniform over all ranks `K ≥ 2`. This is
only the constant comparison in (2.9); its density bound comes from (2.8). -/
theorem isotropic_rank_constant_bound (K : ℕ) (hK : 2 ≤ K)
    {B σ : ℝ} (hB : 0 ≤ B) (hσ : 0 ≤ σ) :
    (K : ℝ) / Real.sqrt 3 * B * σ ≤
      (2 / Real.sqrt 3) * ((K : ℝ) - 1) * B * σ := by
  have hbase : (K : ℝ) / Real.sqrt 3 ≤
      (2 / Real.sqrt 3) * ((K : ℝ) - 1) := by
    calc
      _ ≤ (2 * ((K : ℝ) - 1)) / Real.sqrt 3 :=
        div_le_div_of_nonneg_right (rank_le_twice_rank_sub_one K hK) (Real.sqrt_nonneg 3)
      _ = _ := by ring
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hbase hB) hσ

/-- At rank two the uniform-rank coefficient agrees with the fixed-rank
coefficient, explaining the rank at which the universal comparison is tight. -/
theorem isotropic_rank_two_constant (B σ : ℝ) :
    (2 : ℝ) / Real.sqrt 3 * B * σ =
      (2 / Real.sqrt 3) * ((2 : ℝ) - 1) * B * σ := by norm_num

end Paper35
