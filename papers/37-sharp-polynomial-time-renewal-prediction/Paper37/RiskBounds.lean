import Paper37.PredictorSpec
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Data.ENNReal.BigOperators

namespace Paper37.Prediction
noncomputable section
open scoped BigOperators ENNReal
open Paper37.Renewal MeasureTheory

lemma sum_blockMass (μ : Law) (n : ℕ) :
    ∑ x ∈ (words n).toFinset, blockMass μ x = 1 := by
  rw [List.sum_toFinset _ (words_nodup n)]
  exact blockMass_normalized μ n

lemma sum_ofReal_blockMass (μ : Law) (n : ℕ) :
    ∑ x ∈ (words n).toFinset, ENNReal.ofReal (blockMass μ x) = 1 := by
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => blockMass_nonneg μ x), sum_blockMass]
  simp

lemma hazard_mem_unitInterval (μ : Law) (a : ℕ) :
    0 ≤ μ.mass a / tail μ a ∧ μ.mass a / tail μ a ≤ 1 := by
  constructor
  · exact div_nonneg (μ.nonneg a) (tail_nonneg μ a)
  · by_cases h : tail μ a = 0
    · simp [h]
    · apply (div_le_one (lt_of_le_of_ne (tail_nonneg μ a) (Ne.symm h))).mpr
      linarith [tail_step μ a, tail_nonneg μ (a+1)]

/-- One deterministic fair-coin algorithm is an admissible randomized kernel. -/
def fairPredictor : RandomizedPredictor := fun _ =>
  ⟨Measure.dirac ⟨1/2, by norm_num⟩, Measure.dirac.isProbabilityMeasure⟩

lemma fairPredictor_loss (p : ℝ) :
    (∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl p r.val ∂(fairPredictor []).toMeasure) =
      Boundary.kl p (1/2) := by
  exact lintegral_dirac _ _

/-- The uniform log-2 upper bound is proved for the actual finite stationary
history law and a legitimate probability kernel. -/
theorem risk_fair_le_log_two (μ : Law) (n : ℕ) :
    risk n fairPredictor μ ≤ ENNReal.ofReal (Real.log 2) := by
  unfold risk
  simp only [fairPredictor, ProbabilityMeasure.toMeasure, lintegral_dirac]
  calc
    _ ≤ ∑ x ∈ (words n).toFinset,
        ENNReal.ofReal (blockMass μ x) * ENNReal.ofReal (Real.log 2) := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_left'
      exact Boundary.kl_half_le (conditional_mem_unitInterval μ x).1
        (conditional_mem_unitInterval μ x).2
    _ = _ := by rw [← Finset.sum_mul, sum_ofReal_blockMass, one_mul]

theorem substitutedRisk_fair_le_log_two (μ : Law) (n : ℕ) :
    substitutedRisk n fairPredictor μ ≤ ENNReal.ofReal (Real.log 2) := by
  unfold substitutedRisk
  simp only [fairPredictor, ProbabilityMeasure.toMeasure, lintegral_dirac]
  calc
    _ ≤ ∑ x ∈ (words n).toFinset,
        ENNReal.ofReal (blockMass μ x) * ENNReal.ofReal (Real.log 2) := by
      apply Finset.sum_le_sum
      intro x hx
      apply mul_le_mul_left'
      exact Boundary.kl_half_le (hazard_mem_unitInterval μ _).1
        (hazard_mem_unitInterval μ _).2
    _ = _ := by rw [← Finset.sum_mul, sum_ofReal_blockMass, one_mul]

theorem historywiseRisk_fair_le_log_two (μ : Law) (n : ℕ) :
    historywiseRisk n fairPredictor μ ≤ ENNReal.ofReal (Real.log 2) := by
  apply iSup_le
  intro x
  simp only [fairPredictor, ProbabilityMeasure.toMeasure, lintegral_dirac]
  exact Boundary.kl_half_le (conditional_mem_unitInterval μ x.val).1
    (conditional_mem_unitInterval μ x.val).2

theorem minimaxRisk_le_log_two (n : ℕ) : minimaxRisk n ≤ ENNReal.ofReal (Real.log 2) := by
  exact iInf_le_of_le fairPredictor (iSup_le (fun μ => risk_fair_le_log_two μ n))

theorem substitutedMinimaxRisk_le_log_two (n : ℕ) :
    substitutedMinimaxRisk n ≤ ENNReal.ofReal (Real.log 2) := by
  exact iInf_le_of_le fairPredictor (iSup_le (fun μ => substitutedRisk_fair_le_log_two μ n))

theorem historywiseMinimaxRisk_le_log_two (n : ℕ) :
    historywiseMinimaxRisk n ≤ ENNReal.ofReal (Real.log 2) := by
  exact iInf_le_of_le fairPredictor (iSup_le (fun μ => historywiseRisk_fair_le_log_two μ n))

end
end Paper37.Prediction
