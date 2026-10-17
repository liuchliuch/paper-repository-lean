import Paper37.OccupiedTypesBridge
import Paper37.PartitionEstimate

/-! Averaging the genuine adaptive block regret against the genuine stationary
renewal law. The scalar universal normalizer estimate is kept separate from
the adaptive argument itself. -/
noncomputable section
namespace Paper37.AdaptiveRisk
open scoped BigOperators
open Paper37.Renewal Paper37.Prediction Paper37.Adaptive Paper37.EnvelopeBridge
open Paper37.RenewalOccupancy Paper37.OccupiedTypesBridge Paper37.AnalyticBounds

/-- E.13 from the actual pointwise mixture oracle and the cylinder-derived
stationary occupancy moment. The only explicit input is the separately
established universal envelope normalization estimate. -/
theorem expected_adaptive_regret_le_of_universal (μ : Law) {N : ℕ} (hN : 1 ≤ N)
    (hB : universalPenalty N ≤ redundancyBound N) :
    (∑ x ∈ (words N).toFinset,
      blockMass μ x * Real.log (blockMass μ x/(adaptiveBlock x:ℝ))) ≤
      Real.log 2 + min (redundancyBound N)
        ((2*occupiedComplexity N (fun d => μ.mass (d-1)) (mean μ)+6)*Real.log (N+1:ℝ)) := by
  have hpSum : (∑ x ∈ (words N).toFinset, blockMass μ x) = 1 := by
    rw [← wordSum_eq_sum]
    exact blockMass_normalized μ N
  have hpoint (x : List Bool) (hx : x ∈ (words N).toFinset) :
      blockMass μ x * Real.log (blockMass μ x/(adaptiveBlock x:ℝ)) ≤
        blockMass μ x * (Real.log 2 + min (redundancyBound N) (occupiedPenalty N (kappa x))) := by
    by_cases hp : blockMass μ x = 0
    · simp [hp]
    · have hpos : 0 < blockMass μ x := lt_of_le_of_ne (blockMass_nonneg μ x) (Ne.symm hp)
      have hlen := (mem_words N x).mp (List.mem_toFinset.mp hx)
      have hn : 1 ≤ x.length := by omega
      have hb : universalPenalty x.length ≤ redundancyBound N := by rwa [hlen]
      have hh := adaptive_log_oracle_of_universal μ x hn hpos (redundancyBound N) hb
      rw [hlen] at hh
      exact mul_le_mul_of_nonneg_left hh (blockMass_nonneg μ x)
  have havg : wordSum N (fun x => blockMass μ x *
      min (redundancyBound N) (occupiedPenalty N (kappa x))) ≤
      min (redundancyBound N)
        ((2*occupiedComplexity N (fun d => μ.mass (d-1)) (mean μ)+6)*Real.log (N+1:ℝ)) := by
    have hh := expected_adaptiveOracle_le μ hN
    have heq : wordSum N (fun x => blockMass μ x *
        min (redundancyBound N) (occupiedPenalty N (kappa x))) =
      wordSum N (fun x => blockMass μ x *
        min (redundancyBound N)
          ((2*((max 1 (occupiedTypes N x):ℕ):ℝ)+2)*Real.log (N+1:ℝ) +
            2*Real.log (((max 1 (occupiedTypes N x):ℕ):ℝ)+1))) := by
      apply wordSum_congr
      intro x hx
      simp [occupiedPenalty,kappa,visibleTypes_eq_occupiedTypes x hx]
    rw [heq]
    exact hh
  calc
    _ ≤ ∑ x ∈ (words N).toFinset,
        blockMass μ x * (Real.log 2 + min (redundancyBound N) (occupiedPenalty N (kappa x))) :=
      Finset.sum_le_sum hpoint
    _ = Real.log 2 + wordSum N (fun x => blockMass μ x *
        min (redundancyBound N) (occupiedPenalty N (kappa x))) := by
      rw [wordSum_eq_sum]
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib,← Finset.sum_mul,hpSum,one_mul]
    _ ≤ _ := add_le_add_left havg _

/-- The now-proved classical partition estimate closes the universal branch
without introducing any adaptive assumption. -/
theorem universalPenalty_le_redundancyBound (N : ℕ) :
    universalPenalty N ≤ redundancyBound N := by
  have hZ : (0:ℝ) < ordinaryNormalizer N := by exact_mod_cast Prediction.ordinaryNormalizer_pos N
  have hc : (ordinaryNormalizer N:ℝ) ≤ Paper37.Envelope.cumulativePartitions N := by
    exact_mod_cast ordinaryNormalizer_le_partitions N
  have hb := hc.trans (Paper37.PartitionBound.cumulativePartitions_exp_bound N)
  have hfactor : 0 < 1+2*Real.sqrt (N:ℝ)/partitionConstant := by
    have hh := partitionConstant_pos
    positivity
  have hl := Real.log_le_log hZ hb
  rw [Real.log_mul hfactor.ne' (Real.exp_ne_zero _),Real.log_exp] at hl
  unfold universalPenalty redundancyBound
  rw [Real.log_mul (by positivity) hZ.ne']
  linarith

/-- Full E.4 pointwise oracle E.2, with the paper's explicit B_N. -/
theorem adaptive_log_oracle_source (μ : Law) (x : List Bool) (hN : 1 ≤ x.length)
    (hp : 0 < blockMass μ x) :
    Real.log (blockMass μ x/(adaptiveBlock x:ℝ)) ≤ Real.log 2 +
      min (redundancyBound x.length) (occupiedPenalty x.length (kappa x)) :=
  adaptive_log_oracle_of_universal μ x hN hp _ (universalPenalty_le_redundancyBound _)

/-- Full E.13 for the actual adaptive mixture and stationary renewal law. -/
theorem expected_adaptive_regret_le (μ : Law) {N : ℕ} (hN : 1 ≤ N) :
    (∑ x ∈ (words N).toFinset,
      blockMass μ x * Real.log (blockMass μ x/(adaptiveBlock x:ℝ))) ≤
      Real.log 2 + min (redundancyBound N)
        ((2*occupiedComplexity N (fun d => μ.mass (d-1)) (mean μ)+6)*Real.log (N+1:ℝ)) :=
  expected_adaptive_regret_le_of_universal μ hN (universalPenalty_le_redundancyBound N)

end Paper37.AdaptiveRisk
