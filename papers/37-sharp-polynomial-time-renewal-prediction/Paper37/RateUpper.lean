import Paper37.PartitionEstimate
import Paper37.CompressionPrediction
import Paper37.BoundaryHazard
import Paper37.BoundaryMinimax

/-! Exact statistical upper bound on the actual source predictor. Computability
of its query implementation is a separate contract; no complexity is assumed. -/
noncomputable section
namespace Paper37.RateUpper
open scoped BigOperators ENNReal
open Paper37.Renewal Paper37.Prediction Paper37.EnvelopeBridge
open Paper37.AnalyticBounds Paper37.CompressionPrediction

/-- The complete B.5 bound on the source's exact rational normalizer. -/
theorem ordinaryNormalizer_exp_bound (N : ℕ) :
    (ordinaryNormalizer N : ℝ) ≤
      (1+2*Real.sqrt N/partitionConstant)*Real.exp (partitionConstant*Real.sqrt N) := by
  have hc : (ordinaryNormalizer N : ℝ) ≤ Paper37.Envelope.cumulativePartitions N := by
    exact_mod_cast ordinaryNormalizer_le_partitions N
  exact hc.trans (Paper37.PartitionBound.cumulativePartitions_exp_bound N)

/-- The entire source normalization penalty is at most B_N, with no external
partition estimate or target risk supplied as a premise. -/
theorem normalizer_penalty_le (N : ℕ) :
    Real.log ((N+1 : ℝ)*(ordinaryNormalizer N : ℝ)) ≤ redundancyBound N := by
  have hZ : 0 < (ordinaryNormalizer N : ℝ) := by exact_mod_cast ordinaryNormalizer_pos N
  have hc := partitionConstant_pos
  have ha : 0 < 1+2*Real.sqrt (N : ℝ)/partitionConstant := by positivity
  have hlog := Real.log_le_log hZ (ordinaryNormalizer_exp_bound N)
  rw [Real.log_mul ha.ne' (Real.exp_ne_zero _), Real.log_exp] at hlog
  rw [Real.log_mul (by positivity : (N+1 : ℝ) ≠ 0) hZ.ne']
  unfold redundancyBound
  linarith

/-- Proposition B.2, equation B.8, for every positive source block. -/
theorem pointwise_block_regret (μ : Law) (x : List Bool) (hp : 0 < blockMass μ x) :
    Real.log (blockMass μ x/(blockAssignment x:ℝ)) ≤ redundancyBound x.length :=
  (blockAssignment_log_regret μ x hp).trans (normalizer_penalty_le x.length)

/-- The KL-redundancy conclusion of Proposition B.2 on the true finite law. -/
theorem block_redundancy (μ : Law) (N : ℕ) : blockKL μ N ≤ redundancyBound N :=
  (blockKL_le_log_normalizer μ N).trans (normalizer_penalty_le N)

/-- The exact stationary statistical bound in D.4 for the source predictor D.1. -/
theorem source_risk_upper (μ : Law) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor n hn) μ ≤
      ENNReal.ofReal ((redundancyBound (n+1)+Real.log (n+2))/n) := by
  apply (compression_prediction μ n hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  exact add_le_add_right (block_redundancy μ (n+1)) _

/-- The exact uniform upper risk, preserving the paper's supremum over every
finite-mean gap law and the fixed deterministic algorithm. -/
theorem supremum_source_risk_upper (n : ℕ) (hn : 0 < n) :
    (⨆ μ : Law, risk n (sourcePredictor n hn) μ) ≤
      ENNReal.ofReal ((redundancyBound (n+1)+Real.log (n+2))/n) :=
  iSup_le fun μ => source_risk_upper μ n hn

theorem minimax_le_source_supremum (n : ℕ) (hn : 0 < n) :
    minimaxRisk n ≤ ⨆ μ : Law, risk n (sourcePredictor n hn) μ :=
  iInf_le _ _

/-- Full chain of the statistical upper inequalities in (2.9). The independent
polynomial-bit implementation proof must be joined to this declaration. -/
theorem fixed_time_upper_chain (n : ℕ) (hn : 1 ≤ n) :
    minimaxRisk n ≤ (⨆ μ : Law, risk n (sourcePredictor n (by omega)) μ) ∧
    (⨆ μ : Law, risk n (sourcePredictor n (by omega)) μ) ≤
      ENNReal.ofReal ((redundancyBound (n+1)+Real.log (n+2))/n) ∧
    ENNReal.ofReal ((redundancyBound (n+1)+Real.log (n+2))/n) ≤
      ENNReal.ofReal ((2*Real.pi/Real.sqrt 3+3*Real.sqrt 2)/Real.sqrt n) := by
  exact ⟨minimax_le_source_supremum n (by omega), supremum_source_risk_upper n (by omega),
    ENNReal.ofReal_le_ofReal (fixed_time_explicit_constant hn)⟩

end Paper37.RateUpper
