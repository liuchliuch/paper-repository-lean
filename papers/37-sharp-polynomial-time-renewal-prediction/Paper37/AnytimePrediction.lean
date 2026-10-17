import Paper37.RateUpper
import Paper37.RenewalCountdown
import Mathlib.Data.Nat.Log

/-! The actual horizon-free dyadic restart predictor and its cumulative
stationary conditional KL bound, Appendix G. The algorithm depends only on the
observed history length and the within-epoch prefix. -/
namespace Paper37.AnytimePrediction

open scoped ENNReal

open Finset Compression Compression.Distribution Renewal RenewalCompression RenewalCountdown
open CompressionPrediction Prediction AssignmentConditionals AnalyticBounds

/-- A finite binary outcome kernel defines an admissible deterministic prediction measure. -/
noncomputable def diracPredictor (q : List Bool → Distribution Bool) : RandomizedPredictor := fun x =>
  ⟨MeasureTheory.Measure.dirac ⟨q x true, ⟨(q x).nonneg true, (q x).mass_le_one true⟩⟩,
    MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

lemma binary_eq_distribution (q : Distribution Bool) :
    binary (q true) (q.nonneg true) (q.mass_le_one true) = q := by
  apply Distribution.ext
  intro b
  cases b
  · rw [binary_false]
    have h := q.total
    simp only [Fintype.sum_bool] at h
    linarith
  · rfl

lemma binary_kl_eq_distribution (μ : Law) (x : List Bool) (q : Distribution Bool)
    (hq : ∀ b, 0 < q b) :
    Boundary.kl (conditional μ x) (q true) =
      ENNReal.ofReal (Distribution.kl (next μ x) q) := by
  have hq1 : q true < 1 := by
    have h := q.total
    simp only [Fintype.sum_bool] at h
    linarith [hq false]
  have h := binary_kl_extended (conditional_mem_unitInterval μ x).1
    (conditional_mem_unitInterval μ x).2 (hq true) hq1
  rw [binary_eq_distribution] at h
  exact h

/-- The finite expectation is exactly the source ENNReal conditional risk for
any full-support deterministic binary probability kernel. -/
theorem dirac_risk_eq (μ : Law) (n : ℕ) (q : List Bool → Distribution Bool)
    (hq : ∀ x b, 0 < q x b) :
    risk n (diracPredictor q) μ = ENNReal.ofReal
      (∑ x : Word n, blockMass μ x.val * Distribution.kl (next μ x.val) (q x.val)) := by
  unfold risk
  simp only [diracPredictor, MeasureTheory.ProbabilityMeasure.toMeasure, MeasureTheory.lintegral_dirac]
  simp_rw [binary_kl_eq_distribution μ _ _ (hq _), ← ENNReal.ofReal_mul (blockMass_nonneg μ _)]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => mul_nonneg (blockMass_nonneg μ x)
    (kl_nonneg _ _ (fun b _ => hq x b)))]
  congr 1
  rw [sum_word n (fun x => blockMass μ x * Distribution.kl (next μ x) (q x))]
  exact List.sum_toFinset _ (words_nodup n)

def epochLength (j : ℕ) : ℕ := 2^j

def epochStart (j : ℕ) : ℕ := 2^j - 1

def epochIndex (t : ℕ) : ℕ := Nat.log2 (t + 1)

/-- The history-free schedule uses the next power-of-two epoch. -/
noncomputable def onlineKernel (x : List Bool) : Distribution Bool :=
  kernel (epochLength (epochIndex x.length)) (x.drop (epochStart (epochIndex x.length)))

/-- One single predictor, defined on every finite history without a terminal horizon. -/
noncomputable def predictor : RandomizedPredictor := diracPredictor onlineKernel

/-- Cumulative conditional KL criterion G.1 for the actual stationary renewal law. -/
noncomputable def cumulativeRisk (μ : Law) (N : ℕ) : ℝ≥0∞ :=
  ∑ t ∈ range N, risk t predictor μ

lemma epochLength_pos (j : ℕ) : 0 < epochLength j := by unfold epochLength; positivity

lemma epochStart_add_one (j : ℕ) : epochStart j + 1 = epochLength j := by
  have h := epochLength_pos j
  unfold epochStart epochLength at *
  omega

lemma epochIndex_in_epoch (j r : ℕ) (hr : r < epochLength j) :
    epochIndex (epochStart j + r) = j := by
  unfold epochIndex
  rw [Nat.log2_eq_log_two]
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have h := epochStart_add_one j
    unfold epochLength at h
    omega
  · have h := epochStart_add_one j
    unfold epochLength at hr h
    rw [pow_succ]
    omega

lemma onlineKernel_in_epoch (j r : ℕ) (hr : r < epochLength j) (x : List Bool)
    (hx : x.length = epochStart j + r) :
    onlineKernel x = kernel (epochLength j) (x.drop (epochStart j)) := by
  unfold onlineKernel
  rw [hx, epochIndex_in_epoch j r hr]

lemma memory_nonneg (μ : Law) (k t : ℕ) : 0 ≤ memory μ k t := by
  apply sum_nonneg
  intro s _
  exact mul_nonneg (blockMass_nonneg μ _) (mutualInformation_nonneg _ _)

/-- Each actual epoch step separates into the queried block KL increment and
older-history information. The latter is not silently discarded on restarting. -/
theorem epoch_step_risk (μ : Law) (j r : ℕ) (hr : r < epochLength j) :
    risk (epochStart j + r) predictor μ =
      ENNReal.ofReal (memory μ (epochStart j) r + oneStepRisk μ (epochLength j) r) := by
  unfold predictor
  rw [dirac_risk_eq μ _ onlineKernel (fun x b => kernel_pos _ _ _)]
  have heq : (∑ x : Word (epochStart j + r), blockMass μ x.val *
      Distribution.kl (next μ x.val) (onlineKernel x.val)) =
      ∑ x : Word (epochStart j + r), blockMass μ x.val *
        Distribution.kl (next μ x.val)
          (kernel (epochLength j) (suffixWord x r (by omega)).val) := by
    apply sum_congr rfl
    intro x _
    rw [onlineKernel_in_epoch j r hr x.val x.property]
    simp only [suffixWord, Nat.add_sub_cancel_right]
  rw [heq, full_suffixRisk_decomposition, Nat.add_sub_cancel_right]

/-- The total older-history information charged to an epoch is at most the
entropy of its actual capped first-renewal position. -/
theorem epoch_memory_bound (μ : Law) (k L : ℕ) :
    (∑ t ∈ range L, memory μ k t) ≤ Real.log (L + 1) := by
  calc
    _ ≤ ∑ t ∈ range L, zeroEntropy μ t :=
      sum_le_sum (fun t _ => memory_le_zeroEntropy μ k t)
    _ = entropy (countdown μ L) := sum_zeroEntropy_eq_countdown_entropy μ L
    _ ≤ Real.log (L+1) := by simpa using entropy_le_log_card (countdown μ L)

/-- Each complete dyadic epoch costs at most B_L+log(L+1), on the actual source risk. -/
theorem epoch_risk_bound (μ : Law) (j : ℕ) :
    (∑ r ∈ range (epochLength j), risk (epochStart j + r) predictor μ) ≤
      ENNReal.ofReal (redundancyBound (epochLength j) + Real.log (epochLength j + 1)) := by
  have hstep : ∀ r ∈ range (epochLength j), risk (epochStart j + r) predictor μ =
      ENNReal.ofReal (memory μ (epochStart j) r + oneStepRisk μ (epochLength j) r) :=
    fun r hr => epoch_step_risk μ j r (mem_range.mp hr)
  rw [sum_congr rfl hstep]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun r _ =>
    add_nonneg (memory_nonneg μ _ _) (oneStepRisk_nonneg μ _ _))]
  apply ENNReal.ofReal_le_ofReal
  rw [sum_add_distrib]
  have hm := epoch_memory_bound μ (epochStart j) (epochLength j)
  have hq := sum_oneStepRisk μ (epochLength j) (epochLength j) le_rfl
  change (∑ t ∈ range (epochLength j), oneStepRisk μ (epochLength j) t) =
    blockKL μ (epochLength j) at hq
  rw [hq]
  have hb := RateUpper.block_redundancy μ (epochLength j)
  linarith


lemma epochStart_succ (j : ℕ) : epochStart (j+1) = epochStart j + epochLength j := by
  have hp := epochLength_pos j
  unfold epochStart epochLength at *
  rw [pow_succ]
  omega

/-- Exact reindexing of prediction times into the fixed dyadic epoch schedule. -/
theorem cumulativeRisk_at_epoch_boundary (μ : Law) (K : ℕ) :
    cumulativeRisk μ (epochStart K) =
      ∑ j ∈ range K, ∑ r ∈ range (epochLength j), risk (epochStart j + r) predictor μ := by
  induction K with
  | zero => simp [cumulativeRisk, epochStart]
  | succ K ih =>
    unfold cumulativeRisk
    rw [epochStart_succ, sum_range_add, sum_range_succ]
    change cumulativeRisk μ (epochStart K) + _ = _
    rw [ih]

lemma cumulativeRisk_monotone (μ : Law) : Monotone (cumulativeRisk μ) := by
  intro m n hmn
  exact sum_le_sum_of_subset (range_mono hmn)

lemma epoch_cost_nonneg (L : ℕ) : 0 ≤ redundancyBound L + Real.log (L+1) := by
  have hL : 0 ≤ (L : ℝ) := Nat.cast_nonneg L
  have hs := Real.sqrt_nonneg (L : ℝ)
  have hc := partitionConstant_pos
  have hlog : 0 ≤ Real.log ((L : ℝ)+1) := Real.log_nonneg (by linarith)
  have hr : 0 ≤ 2 * Real.sqrt (L : ℝ) / partitionConstant := by positivity
  have hlog' : 0 ≤ Real.log (1 + 2 * Real.sqrt (L : ℝ) / partitionConstant) :=
    Real.log_nonneg (by linarith)
  unfold redundancyBound
  nlinarith

/-- Complete finite-horizon G.2 epoch-sum bound for one horizon-free predictor. -/
theorem cumulativeRisk_le_epoch_sum (μ : Law) (N : ℕ) (hN : 1 ≤ N) :
    cumulativeRisk μ N ≤ ENNReal.ofReal
      (∑ j ∈ range (Nat.log2 N + 1),
        (redundancyBound (2^j) + Real.log (((2^j : ℕ) : ℝ)+1))) := by
  let J := Nat.log2 N
  have hcap : N ≤ epochStart (J+1) := by
    have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) N
    rw [← Nat.log2_eq_log_two] at h
    unfold epochStart
    dsimp [J]
    omega
  calc
    cumulativeRisk μ N ≤ cumulativeRisk μ (epochStart (J+1)) :=
      cumulativeRisk_monotone μ hcap
    _ = ∑ j ∈ range (J+1), ∑ r ∈ range (epochLength j),
        risk (epochStart j + r) predictor μ := cumulativeRisk_at_epoch_boundary μ (J+1)
    _ ≤ ∑ j ∈ range (J+1), ENNReal.ofReal
        (redundancyBound (epochLength j) + Real.log (epochLength j + 1)) :=
      sum_le_sum (fun j _ => epoch_risk_bound μ j)
    _ = ENNReal.ofReal (∑ j ∈ range (J+1),
        (redundancyBound (epochLength j) + Real.log (epochLength j + 1))) :=
      (ENNReal.ofReal_sum_of_nonneg (fun j _ => epoch_cost_nonneg (epochLength j))).symm
    _ = _ := rfl

/-- The explicit second inequality in G.2, with the paper's minimax-order leading term. -/
theorem cumulativeRisk_upper (μ : Law) (N : ℕ) (hN : 1 ≤ N) :
    cumulativeRisk μ N ≤ ENNReal.ofReal
      (partitionConstant * (2 + Real.sqrt 2) * Real.sqrt N +
        (3 * Real.log 2 / 2) * ((Nat.log2 N : ℝ)+1) * ((Nat.log2 N : ℝ)+2)) := by
  apply (cumulativeRisk_le_epoch_sum μ N hN).trans
  apply ENNReal.ofReal_le_ofReal
  apply dyadic_redundancy_sum_le
  rw [Nat.log2_eq_log_two]
  exact Nat.pow_log_le_self 2 (by omega : N ≠ 0)

/-- Uniformity over the entire source class of finite-mean stationary renewal laws. -/
theorem supremum_cumulativeRisk_upper (N : ℕ) (hN : 1 ≤ N) :
    (⨆ μ : Law, cumulativeRisk μ N) ≤ ENNReal.ofReal
      (partitionConstant * (2 + Real.sqrt 2) * Real.sqrt N +
        (3 * Real.log 2 / 2) * ((Nat.log2 N : ℝ)+1) * ((Nat.log2 N : ℝ)+2)) :=
  iSup_le (fun μ => cumulativeRisk_upper μ N hN)


lemma epochIndex_bounds (t : ℕ) :
    epochLength (epochIndex t) ≤ t+1 ∧ t+1 < 2 * epochLength (epochIndex t) := by
  unfold epochLength epochIndex
  rw [Nat.log2_eq_log_two]
  constructor
  · exact Nat.pow_log_le_self 2 (by omega : t+1 ≠ 0)
  · have h := Nat.lt_pow_succ_log_self (by norm_num : 1 < (2 : ℕ)) (t+1)
    rw [pow_succ] at h
    simpa only [Nat.mul_comm] using h

/-- Every history lies strictly inside its selected scheduled epoch. -/
lemma within_epoch_prefix_lt (x : List Bool) :
    (x.drop (epochStart (epochIndex x.length))).length < epochLength (epochIndex x.length) := by
  have h := epochIndex_bounds x.length
  have hp := epochLength_pos (epochIndex x.length)
  have hs := epochStart_add_one (epochIndex x.length)
  rw [List.length_drop]
  omega

/-- Exact source-query identification of the horizon-free probability. -/
theorem onlineKernel_true (x : List Bool) :
    onlineKernel x true = (blockConditional (epochLength (epochIndex x.length))
      (x.drop (epochStart (epochIndex x.length))) : ℝ) := by
  unfold onlineKernel
  exact kernel_true _ _ (within_epoch_prefix_lt x)

/-- The initial prediction specified in Appendix G is exactly the fair coin. -/
theorem initial_prediction : onlineKernel [] true = 1/2 := by
  rw [onlineKernel_true]
  change (blockConditional 1 [] : ℝ) = 1/2
  rw [Prediction.blockConditional, prefixMass_nil]
  simp only [List.nil_append, div_one]
  rw [prefixMass_full 1 [true] rfl]
  norm_num [blockAssignment, firstSuffix, ordinaryAssignment, ordinaryNormalizer,
    words, wordEnvelope, gapsFrom, Prediction.gapEnvelope]

end Paper37.AnytimePrediction
