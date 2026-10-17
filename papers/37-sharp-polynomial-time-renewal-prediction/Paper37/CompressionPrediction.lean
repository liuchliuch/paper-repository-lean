import Paper37.RenewalCountdown
import Paper37.AssignmentConditionals

namespace Paper37.CompressionPrediction

open Finset Compression Compression.Distribution Renewal RenewalCompression RenewalCountdown
open Prediction EnvelopeBridge AssignmentConditionals

lemma wordSum_snoc (n : ℕ) (f : List Bool → ℝ) :
    wordSum (n + 1) f = wordSum n (fun x => f (x ++ [false]) + f (x ++ [true])) := by
  induction n generalizing f with
  | zero => simp [wordSum_step]
  | succ n ih =>
    calc
      _ = wordSum (n+1) (fun x => f (false::x)) +
          wordSum (n+1) (fun x => f (true::x)) := wordSum_step _ _
      _ = wordSum n (fun x => f (false::(x++[false])) + f (false::(x++[true]))) +
          wordSum n (fun x => f (true::(x++[false])) + f (true::(x++[true]))) := by rw [ih, ih]
      _ = _ := by rw [wordSum_step]; rfl

lemma sum_word_snoc (n : ℕ) (f : List Bool → ℝ) :
    (∑ x : Word (n + 1), f x.val) = ∑ x : Word n, ∑ b : Bool, f (x.val ++ [b]) := by
  rw [sum_word, wordSum_snoc, ← sum_word]
  simp only [Fintype.sum_bool, add_comm]

/-- Prefix marginals of the actual assignment B.7 sum to one. -/
lemma prefixMass_sum (N t : ℕ) (ht : t ≤ N) :
    (∑ x : Word t, (prefixMass N x.val : ℝ)) = 1 := by
  induction t with
  | zero => rw [sum_word 0 (fun z => (prefixMass N z : ℝ))]; simp
  | succ t ih =>
    rw [sum_word_snoc t (fun z => (prefixMass N z : ℝ))]
    calc
      _ = ∑ x : Word t, (prefixMass N x.val : ℝ) := by
        apply sum_congr rfl
        intro x _
        rw [Fintype.sum_bool]
        have hs := prefixMass_step N x.val (by rw [x.property]; omega)
        exact_mod_cast (by linarith [hs] : prefixMass N (x.val ++ [true]) +
          prefixMass N (x.val ++ [false]) = prefixMass N x.val)
      _ = 1 := ih (by omega)

/-- The actual normalized length-`t` prefix law of the source assignment B.7. -/
noncomputable def prefixDistribution (N t : ℕ) (ht : t ≤ N) : Distribution (Word t) where
  mass x := (prefixMass N x.val : ℝ)
  nonneg x := by exact_mod_cast (prefixMass_pos N x.val).le
  total := prefixMass_sum N t ht

@[simp] lemma prefixDistribution_apply (N t : ℕ) (ht : t ≤ N) (x : Word t) :
    prefixDistribution N t ht x = (prefixMass N x.val : ℝ) := rfl

/-- The source block assignment, represented as an actual finite probability law. -/
noncomputable def assignmentDistribution (N : ℕ) : Distribution (Word N) :=
  prefixDistribution N N le_rfl

@[simp] lemma assignmentDistribution_apply (N : ℕ) (x : Word N) :
    assignmentDistribution N x = (blockAssignment x.val : ℝ) := by
  change (prefixMass N x.val : ℝ) = _
  exact_mod_cast prefixMass_full N x.val x.property

/-- Expected conditional KL for the queried source kernel at a prefix length. -/
noncomputable def oneStepRisk (μ : Law) (N t : ℕ) : ℝ :=
  ∑ x : Word t, blockMass μ x.val * Distribution.kl (next μ x.val) (kernel N x.val)

/-- The true full-block KL against the exact B.7 assignment. -/
noncomputable def blockKL (μ : Law) (N : ℕ) : ℝ :=
  Distribution.kl (blockDistribution μ N) (assignmentDistribution N)

/-- One exact KL-chain increment, using the true stationary renewal extension law
and the actual queried prefix law of Q_N. -/
theorem prefixKL_step (μ : Law) (N t : ℕ) (ht : t < N) :
    Distribution.kl (blockDistribution μ (t+1)) (prefixDistribution N (t+1) (by omega)) =
      Distribution.kl (blockDistribution μ t) (prefixDistribution N t ht.le) + oneStepRisk μ N t := by
  have heq : Distribution.kl (blockDistribution μ (t+1)) (prefixDistribution N (t+1) (by omega)) =
      Distribution.kl (joint (blockDistribution μ t) (fun x => next μ x.val))
        (joint (prefixDistribution N t ht.le) (fun x => kernel N x.val)) := by
    unfold Distribution.kl
    simp only [blockDistribution_apply, prefixDistribution_apply]
    rw [sum_word_snoc t (fun z => blockMass μ z *
      (Real.log (blockMass μ z) - Real.log (prefixMass N z : ℝ))), Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro b _
    simp only [joint_apply, blockDistribution_apply, prefixDistribution_apply]
    rw [← weighted_next μ x.val b,
      ← prefixMass_weighted_kernel N x.val (by rw [x.property]; exact ht) b]
  rw [heq, kl_joint_chain_rule]
  · rfl
  · intro x
    change 0 < (prefixMass N x.val : ℝ)
    exact_mod_cast prefixMass_pos N x.val
  · intro x b
    exact kernel_pos N x.val b

/-- The KL chain rule for all prefix queries up to a supplied length. -/
theorem sum_oneStepRisk (μ : Law) (N K : ℕ) (hK : K ≤ N) :
    (∑ t ∈ range K, oneStepRisk μ N t) =
      Distribution.kl (blockDistribution μ K) (prefixDistribution N K hK) := by
  induction K with
  | zero =>
    unfold Distribution.kl
    simp only [blockDistribution_apply, prefixDistribution_apply]
    rw [sum_word 0 (fun z => blockMass μ z *
      (Real.log (blockMass μ z) - Real.log (prefixMass N z : ℝ)))]
    simp [blockMass, stationaryNumerator, residual_zero]
  | succ K ih =>
    rw [sum_range_succ, ih (by omega), prefixKL_step μ N K (by omega)]

lemma oneStepRisk_nonneg (μ : Law) (N t : ℕ) : 0 ≤ oneStepRisk μ N t := by
  apply sum_nonneg
  intro x _
  exact mul_nonneg (blockMass_nonneg μ x.val)
    (kl_nonneg _ _ (fun b _ => kernel_pos N x.val b))

/-- Omitting the first-coordinate KL leaves a quantity bounded by full block KL. -/
theorem suffix_query_KL_budget (μ : Law) (n : ℕ) :
    (∑ t ∈ range n, oneStepRisk μ (n+1) (t+1)) ≤ blockKL μ (n+1) := by
  have h := sum_oneStepRisk μ (n+1) (n+1) le_rfl
  rw [sum_range_succ'] at h
  unfold blockKL assignmentDistribution
  rw [← h]
  exact le_add_of_nonneg_right (oneStepRisk_nonneg μ (n+1) 0)


/-- The exact last-`t` symbols of a length-`n` source history. -/
def suffixWord {n : ℕ} (x : Word n) (t : ℕ) (ht : t ≤ n) : Word t :=
  ⟨x.val.drop (n-t), by rw [List.length_drop, x.property]; omega⟩

/-- Splitting a word at its fixed suffix boundary is a bijection of the actual alphabets. -/
def splitEquiv (n t : ℕ) (ht : t ≤ n) : Word (n-t) × Word t ≃ Word n where
  toFun x := ⟨x.1.val ++ x.2.val, by rw [List.length_append, x.1.property, x.2.property]; omega⟩
  invFun x := (⟨x.val.take (n-t), by rw [List.length_take, x.property]; omega⟩,
    suffixWord x t ht)
  left_inv := by
    rintro ⟨o, s⟩
    apply Prod.ext
    · apply Subtype.ext
      simp [o.property]
    · apply Subtype.ext
      simp [suffixWord, o.property]
  right_inv x := Subtype.ext (List.take_append_drop _ _)

/-- Reindexing the full stationary history by its actual older prefix and suffix. -/
theorem full_suffixRisk_eq (μ : Law) (n t : ℕ) (ht : t ≤ n)
    (q : Word t → Distribution Bool) :
    (∑ x : Word n, blockMass μ x.val *
      Distribution.kl (next μ x.val) (q (suffixWord x t ht))) = suffixRisk μ (n-t) t q := by
  have h := Fintype.sum_equiv (splitEquiv n t ht)
    (fun os => blockMass μ (os.1.val ++ os.2.val) *
      Distribution.kl (next μ (os.1.val ++ os.2.val)) (q os.2))
    (fun x => blockMass μ x.val * Distribution.kl (next μ x.val) (q (suffixWord x t ht)))
    (by rintro ⟨o, s⟩; simp [splitEquiv, suffixWord, o.property])
  rw [Fintype.sum_prod_type, sum_comm] at h
  exact h.symm

/-- Exact loss decomposition at each source suffix query. -/
theorem full_suffixRisk_decomposition (μ : Law) (N n t : ℕ) (ht : t ≤ n) :
    (∑ x : Word n, blockMass μ x.val *
      Distribution.kl (next μ x.val) (kernel N (suffixWord x t ht).val)) =
      memory μ (n-t) t + oneStepRisk μ N t := by
  rw [full_suffixRisk_eq μ n t ht (fun s => kernel N s.val), suffixRisk_decomposition]
  rfl

lemma sum_fin_succ (n : ℕ) (f : ℕ → ℝ) :
    (∑ t : Fin n, f (t.val + 1)) = ∑ t ∈ Icc 1 n, f t := by
  classical
  refine sum_bij (fun t _ => t.val + 1) ?_ ?_ ?_ ?_
  · intro t _
    dsimp only
    exact mem_Icc.mpr ⟨by omega, by have := t.is_lt; omega⟩
  · intro t _ u _ h
    dsimp only at h
    apply Fin.ext
    omega
  · intro u hu
    have hu := mem_Icc.mp hu
    exact ⟨⟨u-1, by omega⟩, mem_univ _, by simp; omega⟩
  · intro t _
    rfl

/-- The actual suffix-averaged prediction as a probability law on the binary outcome. -/
noncomputable def averageKernel (n : ℕ) (hn : 0 < n) (x : Word n) : Distribution Bool := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact mixture (uniform (α := Fin n))
    (fun t => kernel (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val)

/-- The binary probability in the averaged kernel is exactly the rational D.1 implementation. -/
theorem averageKernel_true (n : ℕ) (hn : 0 < n) (x : Word n) :
    averageKernel n hn x true = (predict n x.val : ℝ) := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hk : ∀ t : Fin n, kernel (n+1)
      (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val true =
      (blockConditional (n+1) (x.val.drop (n-(t.val+1))) : ℝ) := by
    intro t
    rw [kernel_true]
    · rfl
    · rw [(suffixWord x (t.val+1) (by have := t.is_lt; omega)).property]
      have := t.is_lt
      omega
  unfold averageKernel
  simp only [mixture_apply, uniform_apply, Fintype.card_fin]
  simp_rw [hk]
  rw [← mul_sum, sum_fin_succ n (fun t => (blockConditional (n+1) (x.val.drop (n-t)) : ℝ))]
  unfold predict
  push_cast
  ring

lemma averageKernel_pos (n : ℕ) (hn : 0 < n) (x : Word n) (b : Bool) :
    0 < averageKernel n hn x b := by
  letI : NeZero n := ⟨hn.ne'⟩
  unfold averageKernel
  apply mixture_pos _ _ ⟨0, hn⟩ b
  · simp only [uniform_apply, Fintype.card_fin]
    exact inv_pos.mpr (Nat.cast_pos.mpr hn)
  · exact kernel_pos _ _ _

/-- Lemma D.2 for the actual stationary renewal law and the exact source Q_N.
The predictor is the suffix average D.1 and the block term is genuine finite KL. -/
theorem compression_prediction_real (μ : Law) (n : ℕ) (hn : 0 < n) :
    (∑ x : Word n, blockMass μ x.val *
      Distribution.kl (next μ x.val) (averageKernel n hn x)) ≤
      (blockKL μ (n+1) + Real.log (n+2)) / n := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hj : ∀ x : Word n, Distribution.kl (next μ x.val) (averageKernel n hn x) ≤
      (n : ℝ)⁻¹ * ∑ t : Fin n, Distribution.kl (next μ x.val)
        (kernel (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val) := by
    intro x
    have h := kl_mixture_right_le (uniform (α := Fin n)) (next μ x.val)
      (fun t => kernel (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val)
      (fun t b => kernel_pos _ _ _)
    simpa only [averageKernel, uniform_apply, Fintype.card_fin, ← mul_sum] using h
  calc
    _ ≤ ∑ x : Word n, blockMass μ x.val * ((n : ℝ)⁻¹ *
        ∑ t : Fin n, Distribution.kl (next μ x.val)
          (kernel (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val)) :=
      sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hj x) (blockMass_nonneg μ x.val))
    _ = (n : ℝ)⁻¹ * ∑ t : Fin n, ∑ x : Word n, blockMass μ x.val *
        Distribution.kl (next μ x.val)
          (kernel (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro x _
      ring
    _ = (n : ℝ)⁻¹ * ((∑ t : Fin n, memory μ (n-(t.val+1)) (t.val+1)) +
        ∑ t : Fin n, oneStepRisk μ (n+1) (t.val+1)) := by
      simp_rw [full_suffixRisk_decomposition, sum_add_distrib]
    _ ≤ (n : ℝ)⁻¹ * (Real.log (n+2) + blockKL μ (n+1)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      apply add_le_add
      · rw [Fin.sum_univ_eq_sum_range (fun t => memory μ (n-(t+1)) (t+1))]
        exact renewal_memory_sum_bound μ n (fun t => n-t)
      · rw [Fin.sum_univ_eq_sum_range (fun t => oneStepRisk μ (n+1) (t+1))]
        exact suffix_query_KL_budget μ n
    _ = _ := by ring


/-- The exact rational source predictor is interior on every source history. -/
theorem predict_interior (n : ℕ) (hn : 0 < n) (x : List Bool) (hx : x.length = n) :
    0 < (predict n x : ℝ) ∧ (predict n x : ℝ) < 1 := by
  let w : Word n := ⟨x, hx⟩
  have hp := averageKernel_pos n hn w true
  have hf := averageKernel_pos n hn w false
  have ht := (averageKernel n hn w).total
  simp only [Fintype.sum_bool] at ht
  rw [averageKernel_true] at hp ht
  exact ⟨hp, by linarith⟩

/-- The averaged outcome law is exactly Bernoulli with the implemented D.1 parameter. -/
theorem averageKernel_binary (n : ℕ) (hn : 0 < n) (x : Word n) :
    averageKernel n hn x = binary (predict n x.val : ℝ)
      (predict_interior n hn x.val x.property).1.le
      (predict_interior n hn x.val x.property).2.le := by
  apply Distribution.ext
  intro b
  have ht := (averageKernel n hn x).total
  simp only [Fintype.sum_bool] at ht
  cases b
  · rw [binary_false]
    rw [averageKernel_true] at ht
    linarith
  · exact averageKernel_true n hn x

lemma average_loss_eq (μ : Law) (n : ℕ) (hn : 0 < n) (x : Word n) :
    Distribution.kl (next μ x.val) (averageKernel n hn x) =
      Boundary.klReal (conditional μ x.val) (predict n x.val : ℝ) := by
  rw [averageKernel_binary]
  exact binary_klReal (conditional_mem_unitInterval μ x.val).1
    (conditional_mem_unitInterval μ x.val).2
    (predict_interior n hn x.val x.property).1 (predict_interior n hn x.val x.property).2

lemma implemented_loss_nonneg (μ : Law) (n : ℕ) (hn : 0 < n)
    (x : List Bool) (hx : x.length = n) :
    0 ≤ Boundary.klReal (conditional μ x) (predict n x : ℝ) := by
  rw [← average_loss_eq μ n hn ⟨x, hx⟩]
  exact kl_nonneg _ _ (fun b _ => averageKernel_pos n hn ⟨x, hx⟩ b)

/-- The deterministic implementation as an admissible privately randomized predictor.
The off-length version is a fair coin; only length-`n` histories enter `Prediction.risk`. -/
noncomputable def sourcePredictor (n : ℕ) (hn : 0 < n) : RandomizedPredictor := fun x =>
  if hx : x.length = n then
    ⟨MeasureTheory.Measure.dirac ⟨(predict n x : ℝ),
      ⟨(predict_interior n hn x hx).1.le, (predict_interior n hn x hx).2.le⟩⟩,
      MeasureTheory.Measure.dirac.isProbabilityMeasure⟩
  else ⟨MeasureTheory.Measure.dirac ⟨1/2, by norm_num⟩,
    MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

/-- Exact bridge from the source ENNReal risk to the finite probability calculation.
Full-support source predictions ensure that no infinite KL term is discarded. -/
theorem source_risk_eq (μ : Law) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor n hn) μ = ENNReal.ofReal
      (∑ x : Word n, blockMass μ x.val *
        Distribution.kl (next μ x.val) (averageKernel n hn x)) := by
  unfold risk
  calc
    _ = ∑ x ∈ (words n).toFinset, ENNReal.ofReal
        (blockMass μ x * Boundary.klReal (conditional μ x) (predict n x : ℝ)) := by
      apply sum_congr rfl
      intro x hx
      have hlen : x.length = n := (mem_words n x).mp (List.mem_toFinset.mp hx)
      have hi := predict_interior n hn x hlen
      simp only [sourcePredictor, hlen, ↓reduceDIte, MeasureTheory.ProbabilityMeasure.toMeasure,
        MeasureTheory.lintegral_dirac]
      rw [Boundary.kl, if_neg (by simp [hi.1.ne', ne_of_lt hi.2])]
      exact (ENNReal.ofReal_mul (blockMass_nonneg μ x)).symm
    _ = ENNReal.ofReal (∑ x ∈ (words n).toFinset,
        blockMass μ x * Boundary.klReal (conditional μ x) (predict n x : ℝ)) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun x hx => mul_nonneg (blockMass_nonneg μ x)
        (implemented_loss_nonneg μ n hn x ((mem_words n x).mp (List.mem_toFinset.mp hx))))).symm
    _ = _ := by
      congr 1
      simp_rw [average_loss_eq]
      rw [sum_word n (fun x => blockMass μ x * Boundary.klReal (conditional μ x) (predict n x : ℝ))]
      exact List.sum_toFinset _ (words_nodup n)

/-- Original D.2, including the source's actual ENNReal risk and implemented predictor. -/
theorem compression_prediction (μ : Law) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor n hn) μ ≤
      ENNReal.ofReal ((blockKL μ (n+1) + Real.log (n+2)) / n) := by
  rw [source_risk_eq]
  exact ENNReal.ofReal_le_ofReal (compression_prediction_real μ n hn)

/-- The block term in D.2 is exactly the source KL redundancy expression. -/
theorem blockKL_eq_source_sum (μ : Law) (N : ℕ) :
    blockKL μ N = ∑ x ∈ (words N).toFinset,
      blockMass μ x * Real.log (blockMass μ x / (blockAssignment x : ℝ)) := by
  unfold blockKL Distribution.kl
  simp only [blockDistribution_apply, assignmentDistribution_apply]
  calc
    _ = ∑ x : Word N, blockMass μ x.val *
        Real.log (blockMass μ x.val / (blockAssignment x.val : ℝ)) := by
      apply sum_congr rfl
      intro x _
      by_cases hp : blockMass μ x.val = 0
      · simp [hp]
      · rw [Real.log_div hp (by exact_mod_cast (blockAssignment_pos x.val).ne')]
    _ = _ := by
      rw [sum_word N (fun x => blockMass μ x * Real.log (blockMass μ x / (blockAssignment x : ℝ)))]
      exact (List.sum_toFinset _ (words_nodup N)).symm

/-- Proposition B.2 supplies the genuine block KL input of D.2. -/
theorem blockKL_le_log_normalizer (μ : Law) (N : ℕ) :
    blockKL μ N ≤ Real.log ((N+1 : ℝ) * (ordinaryNormalizer N : ℝ)) := by
  rw [blockKL_eq_source_sum]
  exact blockAssignment_redundancy_bound μ N

/-- The stationary risk of the actual polynomial-query predictor, with the exact
finite normalizer before the analytic partition estimate is substituted. -/
theorem source_risk_le_log_normalizer (μ : Law) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor n hn) μ ≤ ENNReal.ofReal
      ((Real.log ((n+2 : ℝ) * (ordinaryNormalizer (n+1) : ℝ)) + Real.log (n+2)) / n) := by
  apply (compression_prediction μ n hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply add_le_add_right
  have h := blockKL_le_log_normalizer μ (n+1)
  simpa only [Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h

/-- The same finite upper bound holds for the minimax risk with all privately
randomized predictors allowed in the infimum. -/
theorem minimaxRisk_le_log_normalizer (n : ℕ) (hn : 0 < n) :
    minimaxRisk n ≤ ENNReal.ofReal
      ((Real.log ((n+2 : ℝ) * (ordinaryNormalizer (n+1) : ℝ)) + Real.log (n+2)) / n) := by
  exact iInf_le_of_le (sourcePredictor n hn) (iSup_le (fun μ => source_risk_le_log_normalizer μ n hn))

end Paper37.CompressionPrediction
