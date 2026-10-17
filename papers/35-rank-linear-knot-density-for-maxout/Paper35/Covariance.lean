import Paper35.Assembly
import Paper35.Gini
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The covariance specialization of the genuine weighted model

The directional Gini functional uses the canonical product of the actual
normalized tilted law. Its variance estimate follows from the sharp real
Gini inequality, using only the source finite-covariance assumption.
The last result is a conditional assembly from the visibility theorem.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal

namespace Paper35.Source.WeightedModel
variable {d : ℕ}

/-- Finite covariance of the tilted vector implies an L² moment for every
projected scalar variable. -/
theorem projected_memLp_two (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (u : Space d) :
    MemLp (fun w => inner ℝ u w) 2 m.tilted := hW.const_inner u

/-- The covariance quadratic form in the source model is exactly the
variance of the corresponding scalar projection. -/
theorem projectedVariance_eq_variance (m : WeightedModel d) (u : Space d) :
    m.projectedVariance u = variance (fun w => inner ℝ u w) m.tilted := by
  rw [variance_eq_integral (by fun_prop)]
  rfl

/-- Identify the nonnegative iterated source integral with the canonical
product-law Gini mean difference, including the source moment justification. -/
theorem directionalGini_eq_ofReal_meanDifference (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (u : Space d) :
    m.directionalGini u =
      ENNReal.ofReal (Paper35.Gini.meanDifference m.tilted (fun w => inner ℝ u w)) := by
  have hX : Measurable (fun w : Space d => inner ℝ u w) := by fun_prop
  have hXi : Integrable (fun w => inner ℝ u w) m.tilted :=
    (m.projected_memLp_two hW u).integrable (by norm_num)
  have hpair : Integrable (fun p : Space d × Space d =>
      |inner ℝ u p.1 - inner ℝ u p.2|) (m.tilted.prod m.tilted) :=
    ((hXi.comp_fst m.tilted).sub (hXi.comp_snd m.tilted)).abs
  calc
    m.directionalGini u = ∫⁻ p : Space d × Space d,
        ENNReal.ofReal |inner ℝ u p.1 - inner ℝ u p.2| ∂m.tilted.prod m.tilted := by
      have hm : Measurable (fun p : Space d × Space d =>
          ENNReal.ofReal |inner ℝ u p.1 - inner ℝ u p.2|) := by
        simpa only [Real.norm_eq_abs] using ((hX.comp measurable_fst).sub
          (hX.comp measurable_snd)).norm.ennreal_ofReal
      rw [lintegral_prod (fun p : Space d × Space d =>
        ENNReal.ofReal |inner ℝ u p.1 - inner ℝ u p.2|) hm.aemeasurable]
      simp only [directionalGini, inner_sub_right]
    _ = ENNReal.ofReal (Paper35.Gini.meanDifference m.tilted (fun w => inner ℝ u w)) := by
      exact (ofReal_integral_eq_lintegral_ofReal hpair
        (Filter.Eventually.of_forall fun p => abs_nonneg _)).symm

/-- Equation (5.2) for the actual tilted weight law and covariance quadratic
form. The only moment assumption is the source finite-covariance condition. -/
theorem directionalGini_le_sqrt_projectedVariance (m : WeightedModel d)
    (hW : MemLp (fun w => w) 2 m.tilted) (u : Space d) :
    m.directionalGini u ≤ ENNReal.ofReal (2 / Real.sqrt 3) *
      ENNReal.ofReal (Real.sqrt (m.projectedVariance u)) := by
  rw [directionalGini_eq_ofReal_meanDifference m hW u,
    ← ENNReal.ofReal_mul (by positivity : 0 ≤ (2 : ℝ) / Real.sqrt 3)]
  apply ENNReal.ofReal_le_ofReal
  rw [projectedVariance_eq_variance]
  exact Paper35.Gini.sharp_gini_product m.tilted (fun w => inner ℝ u w)
    (by fun_prop) (m.projected_memLp_two hW u)

/-- Cancellation of the factor two in the sharp Gini inequality with the
visibility coefficient, valid even when the remaining mass is infinite. -/
theorem covariance_coefficient_cancellation (A : ℝ≥0∞) :
    (A / 2) * ENNReal.ofReal (2 / Real.sqrt 3) =
      A / ENNReal.ofReal (Real.sqrt 3) := by
  rw [ENNReal.ofReal_div_of_pos (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3))]
  rw [show ENNReal.ofReal (2 : ℝ) = 2 by norm_num]
  simp only [div_eq_mul_inv]
  calc
    _ = (A * (ENNReal.ofReal (Real.sqrt 3))⁻¹) * ((2 : ℝ≥0∞)⁻¹ * 2) := by ac_rfl
    _ = _ := by
      rw [ENNReal.inv_mul_cancel (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        ENNReal.ofNat_ne_top, mul_one]

/-- Integral assembly of (2.7) from (2.6), with its original finite tilted
covariance assumption. This is conditional on `WeightedVisibilityClaim`. -/
theorem weightedCovariance_of_weightedVisibility
    (hvisibility : WeightedVisibilityClaim (d := d)) :
    WeightedCovarianceClaim (d := d) := by
  intro m hW K hK p
  calc
    m.expectedCount K p ≤ ((K : ℝ≥0∞) * m.average / 2) *
        ∫⁻ s in Icc 0 p.length, m.directionalGini (deriv p.curve s) :=
      hvisibility m K hK p
    _ ≤ ((K : ℝ≥0∞) * m.average / 2) * ∫⁻ s in Icc 0 p.length,
        ENNReal.ofReal (2 / Real.sqrt 3) *
          ENNReal.ofReal (Real.sqrt (m.projectedVariance (deriv p.curve s))) := by
      apply mul_le_mul_left'
      exact lintegral_mono fun s =>
        m.directionalGini_le_sqrt_projectedVariance hW (deriv p.curve s)
    _ = ((K : ℝ≥0∞) * m.average / 2) * (ENNReal.ofReal (2 / Real.sqrt 3) *
        ∫⁻ s in Icc 0 p.length,
          ENNReal.ofReal (Real.sqrt (m.projectedVariance (deriv p.curve s)))) := by
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ((K : ℝ≥0∞) * m.average / ENNReal.ofReal (Real.sqrt 3)) *
        ∫⁻ s in Icc 0 p.length,
          ENNReal.ofReal (Real.sqrt (m.projectedVariance (deriv p.curve s))) := by
      rw [← mul_assoc, covariance_coefficient_cancellation]

end Paper35.Source.WeightedModel
