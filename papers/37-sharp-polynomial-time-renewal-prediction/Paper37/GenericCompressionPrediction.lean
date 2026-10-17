import Paper37.CompressionPrediction

/-! Generic compression-to-prediction for actual normalized full-support binary
assignments. The structural inputs are masses, positivity, and normalization;
no prediction inequality or regeneration property is an input. -/
namespace Paper37.GenericCompressionPrediction

open Finset Compression Compression.Distribution Renewal RenewalCompression RenewalCountdown
open CompressionPrediction Prediction

/-- A normalized full-support assignment on every finite binary alphabet. -/
structure Assignment where
  mass : List Bool → ℚ
  positive : ∀ x, 0 < mass x
  normalized : ∀ N, (∑ x ∈ (words N).toFinset, mass x) = 1

variable (A : Assignment)

noncomputable def prefixMass (N : ℕ) (z : List Bool) : ℚ :=
  ∑ v ∈ (words (N-z.length)).toFinset, A.mass (z ++ v)

noncomputable def blockConditional (N : ℕ) (z : List Bool) : ℚ :=
  prefixMass A N (z ++ [true]) / prefixMass A N z

noncomputable def predict (n : ℕ) (x : List Bool) : ℚ :=
  (∑ t ∈ Icc 1 n, blockConditional A (n+1) (x.drop (n-t))) / n

lemma prefixMass_step (N : ℕ) (z : List Bool) (hz : z.length < N) :
    prefixMass A N z = prefixMass A N (z ++ [false]) + prefixMass A N (z ++ [true]) := by
  unfold prefixMass
  have hrem : N-z.length = (N-(z.length+1))+1 := by omega
  rw [hrem, EnvelopeBridge.sum_words_step]
  simp [List.append_assoc]

lemma prefixMass_pos (N : ℕ) (z : List Bool) : 0 < prefixMass A N z := by
  apply Finset.sum_pos'
  · intro v hv
    exact (A.positive _).le
  · refine ⟨List.replicate (N-z.length) false, ?_, A.positive _⟩
    exact List.mem_toFinset.mpr ((mem_words _ _).mpr (by simp))

@[simp] theorem prefixMass_nil (N : ℕ) : prefixMass A N [] = 1 := by
  simpa [prefixMass] using A.normalized N

lemma prefixMass_full (N : ℕ) (x : List Bool) (hx : x.length = N) :
    prefixMass A N x = A.mass x := by
  simp [prefixMass, hx, words]

/-- Every queried conditional before its horizon is a genuine interior probability. -/
theorem blockConditional_interior (N : ℕ) (z : List Bool) (hz : z.length < N) :
    0 < blockConditional A N z ∧ blockConditional A N z < 1 := by
  have hp := prefixMass_pos A N z
  have ht := prefixMass_pos A N (z ++ [true])
  have hf := prefixMass_pos A N (z ++ [false])
  constructor
  · exact div_pos ht hp
  · unfold blockConditional
    apply (div_lt_one hp).mpr
    rw [prefixMass_step A N z hz]
    linarith

/-- A horizon-specific source conditional, extended by fair coins after the horizon. -/
noncomputable def kernel (N : ℕ) (z : List Bool) : Distribution Bool :=
  if hz : z.length < N then
    binary (blockConditional A N z : ℝ)
      (by exact_mod_cast (blockConditional_interior A N z hz).1.le)
      (by exact_mod_cast (blockConditional_interior A N z hz).2.le)
  else binary (1/2) (by norm_num) (by norm_num)

lemma kernel_pos (N : ℕ) (z : List Bool) (b : Bool) : 0 < kernel A N z b := by
  unfold kernel
  split_ifs with hz
  · have h := blockConditional_interior A N z hz
    cases b
    · simp only [binary_false]
      have : (blockConditional A N z : ℝ) < 1 := by exact_mod_cast h.2
      linarith
    · simp only [binary_true]
      exact_mod_cast h.1
  · cases b <;> norm_num

lemma kernel_true (N : ℕ) (z : List Bool) (hz : z.length < N) :
    kernel A N z true = (blockConditional A N z : ℝ) := by
  simp [kernel, hz]

/-- The prefix kernel A recovers each true prefix probability exactly. -/
theorem prefixMass_weighted_kernel (N : ℕ) (z : List Bool) (hz : z.length < N) (b : Bool) :
    (prefixMass A N z : ℝ) * kernel A N z b = (prefixMass A N (z ++ [b]) : ℝ) := by
  have hp : (prefixMass A N z : ℝ) ≠ 0 := by exact_mod_cast (prefixMass_pos A N z).ne'
  have ht : (prefixMass A N z : ℝ) * (blockConditional A N z : ℝ) =
      (prefixMass A N (z ++ [true]) : ℝ) := by
    push_cast [blockConditional]
    exact mul_div_cancel₀ _ hp
  cases b
  · simp only [kernel, hz, ↓reduceDIte, binary_false]
    have hs := prefixMass_step A N z hz
    have hs' : (prefixMass A N z : ℝ) = (prefixMass A N (z ++ [false]) : ℝ) +
      (prefixMass A N (z ++ [true]) : ℝ) := by exact_mod_cast hs
    nlinarith
  · rw [kernel_true A N z hz]
    exact ht


lemma prefixMass_sum (N t : ℕ) (ht : t ≤ N) :
    (∑ x : Word t, (prefixMass A N x.val : ℝ)) = 1 := by
  induction t with
  | zero => rw [sum_word 0 (fun z => (prefixMass A N z : ℝ))]; simp
  | succ t ih =>
    rw [sum_word_snoc t (fun z => (prefixMass A N z : ℝ))]
    calc
      _ = ∑ x : Word t, (prefixMass A N x.val : ℝ) := by
        apply sum_congr rfl
        intro x _
        rw [Fintype.sum_bool]
        have hs := prefixMass_step A N x.val (by rw [x.property]; omega)
        exact_mod_cast (by linarith [hs] : prefixMass A N (x.val ++ [true]) +
          prefixMass A N (x.val ++ [false]) = prefixMass A N x.val)
      _ = 1 := ih (by omega)

noncomputable def prefixDistribution (N t : ℕ) (ht : t ≤ N) : Distribution (Word t) where
  mass x := (prefixMass A N x.val : ℝ)
  nonneg x := by exact_mod_cast (prefixMass_pos A N x.val).le
  total := prefixMass_sum A N t ht

@[simp] lemma prefixDistribution_apply (N t : ℕ) (ht : t ≤ N) (x : Word t) :
    prefixDistribution A N t ht x = (prefixMass A N x.val : ℝ) := rfl

noncomputable def assignmentDistribution (N : ℕ) : Distribution (Word N) :=
  prefixDistribution A N N le_rfl

@[simp] lemma assignmentDistribution_apply (N : ℕ) (x : Word N) :
    assignmentDistribution A N x = (A.mass x.val : ℝ) := by
  change (prefixMass A N x.val : ℝ) = _
  exact_mod_cast prefixMass_full A N x.val x.property

noncomputable def oneStepRisk (μ : Law) (N t : ℕ) : ℝ :=
  ∑ x : Word t, blockMass μ x.val * Distribution.kl (next μ x.val) (kernel A N x.val)

noncomputable def blockKL (μ : Law) (N : ℕ) : ℝ :=
  Distribution.kl (blockDistribution μ N) (assignmentDistribution A N)

theorem prefixKL_step (μ : Law) (N t : ℕ) (ht : t < N) :
    Distribution.kl (blockDistribution μ (t+1)) (prefixDistribution A N (t+1) (by omega)) =
      Distribution.kl (blockDistribution μ t) (prefixDistribution A N t ht.le) + oneStepRisk A μ N t := by
  have heq : Distribution.kl (blockDistribution μ (t+1)) (prefixDistribution A N (t+1) (by omega)) =
      Distribution.kl (joint (blockDistribution μ t) (fun x => next μ x.val))
        (joint (prefixDistribution A N t ht.le) (fun x => kernel A N x.val)) := by
    unfold Distribution.kl
    simp only [blockDistribution_apply, prefixDistribution_apply A]
    rw [sum_word_snoc t (fun z => blockMass μ z *
      (Real.log (blockMass μ z) - Real.log (prefixMass A N z : ℝ))), Fintype.sum_prod_type]
    apply sum_congr rfl
    intro x _
    apply sum_congr rfl
    intro b _
    simp only [joint_apply, blockDistribution_apply, prefixDistribution_apply A]
    rw [← weighted_next μ x.val b,
      ← prefixMass_weighted_kernel A N x.val (by rw [x.property]; exact ht) b]
  rw [heq, kl_joint_chain_rule]
  · rfl
  · intro x
    change 0 < (prefixMass A N x.val : ℝ)
    exact_mod_cast prefixMass_pos A N x.val
  · intro x b
    exact kernel_pos A N x.val b

theorem sum_oneStepRisk (μ : Law) (N K : ℕ) (hK : K ≤ N) :
    (∑ t ∈ range K, oneStepRisk A μ N t) =
      Distribution.kl (blockDistribution μ K) (prefixDistribution A N K hK) := by
  induction K with
  | zero =>
    unfold Distribution.kl
    simp only [blockDistribution_apply, prefixDistribution_apply A]
    rw [sum_word 0 (fun z => blockMass μ z *
      (Real.log (blockMass μ z) - Real.log (prefixMass A N z : ℝ)))]
    simp [blockMass, stationaryNumerator, residual_zero]
  | succ K ih =>
    rw [sum_range_succ, ih (by omega), prefixKL_step A μ N K (by omega)]

lemma oneStepRisk_nonneg (μ : Law) (N t : ℕ) : 0 ≤ oneStepRisk A μ N t := by
  apply sum_nonneg
  intro x _
  exact mul_nonneg (blockMass_nonneg μ x.val)
    (kl_nonneg _ _ (fun b _ => kernel_pos A N x.val b))

theorem suffix_query_KL_budget (μ : Law) (n : ℕ) :
    (∑ t ∈ range n, oneStepRisk A μ (n+1) (t+1)) ≤ blockKL A μ (n+1) := by
  have h := sum_oneStepRisk A μ (n+1) (n+1) le_rfl
  rw [sum_range_succ'] at h
  unfold blockKL assignmentDistribution
  rw [← h]
  exact le_add_of_nonneg_right (oneStepRisk_nonneg A μ (n+1) 0)

theorem full_suffixRisk_decomposition (μ : Law) (N n t : ℕ) (ht : t ≤ n) :
    (∑ x : Word n, blockMass μ x.val *
      Distribution.kl (next μ x.val) (kernel A N (suffixWord x t ht).val)) =
      memory μ (n-t) t + oneStepRisk A μ N t := by
  rw [full_suffixRisk_eq μ n t ht (fun s => kernel A N s.val), suffixRisk_decomposition]
  rfl

noncomputable def averageKernel (n : ℕ) (hn : 0 < n) (x : Word n) : Distribution Bool := by
  letI : NeZero n := ⟨hn.ne'⟩
  exact mixture (uniform (α := Fin n))
    (fun t => kernel A (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val)

theorem averageKernel_true (n : ℕ) (hn : 0 < n) (x : Word n) :
    averageKernel A n hn x true = (predict A n x.val : ℝ) := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hk : ∀ t : Fin n, kernel A (n+1)
      (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val true =
      (blockConditional A (n+1) (x.val.drop (n-(t.val+1))) : ℝ) := by
    intro t
    rw [kernel_true A]
    · rfl
    · rw [(suffixWord x (t.val+1) (by have := t.is_lt; omega)).property]
      have := t.is_lt
      omega
  unfold averageKernel
  simp only [mixture_apply, uniform_apply, Fintype.card_fin]
  simp_rw [hk]
  rw [← mul_sum, sum_fin_succ n (fun t => (blockConditional A (n+1) (x.val.drop (n-t)) : ℝ))]
  unfold predict
  push_cast
  ring

lemma averageKernel_pos (n : ℕ) (hn : 0 < n) (x : Word n) (b : Bool) :
    0 < averageKernel A n hn x b := by
  letI : NeZero n := ⟨hn.ne'⟩
  unfold averageKernel
  apply mixture_pos _ _ ⟨0, hn⟩ b
  · simp only [uniform_apply, Fintype.card_fin]
    exact inv_pos.mpr (Nat.cast_pos.mpr hn)
  · exact kernel_pos A _ _ _

theorem compression_prediction_real (μ : Law) (n : ℕ) (hn : 0 < n) :
    (∑ x : Word n, blockMass μ x.val *
      Distribution.kl (next μ x.val) (averageKernel A n hn x)) ≤
      (blockKL A μ (n+1) + Real.log (n+2)) / n := by
  letI : NeZero n := ⟨hn.ne'⟩
  have hj : ∀ x : Word n, Distribution.kl (next μ x.val) (averageKernel A n hn x) ≤
      (n : ℝ)⁻¹ * ∑ t : Fin n, Distribution.kl (next μ x.val)
        (kernel A (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val) := by
    intro x
    have h := kl_mixture_right_le (uniform (α := Fin n)) (next μ x.val)
      (fun t => kernel A (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val)
      (fun t b => kernel_pos A _ _ _)
    simpa only [averageKernel, uniform_apply, Fintype.card_fin, ← mul_sum] using h
  calc
    _ ≤ ∑ x : Word n, blockMass μ x.val * ((n : ℝ)⁻¹ *
        ∑ t : Fin n, Distribution.kl (next μ x.val)
          (kernel A (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val)) :=
      sum_le_sum (fun x _ => mul_le_mul_of_nonneg_left (hj x) (blockMass_nonneg μ x.val))
    _ = (n : ℝ)⁻¹ * ∑ t : Fin n, ∑ x : Word n, blockMass μ x.val *
        Distribution.kl (next μ x.val)
          (kernel A (n+1) (suffixWord x (t.val+1) (by have := t.is_lt; omega)).val) := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro t _
      apply sum_congr rfl
      intro x _
      ring
    _ = (n : ℝ)⁻¹ * ((∑ t : Fin n, memory μ (n-(t.val+1)) (t.val+1)) +
        ∑ t : Fin n, oneStepRisk A μ (n+1) (t.val+1)) := by
      simp_rw [full_suffixRisk_decomposition A, sum_add_distrib]
    _ ≤ (n : ℝ)⁻¹ * (Real.log (n+2) + blockKL A μ (n+1)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      apply add_le_add
      · rw [Fin.sum_univ_eq_sum_range (fun t => memory μ (n-(t+1)) (t+1))]
        exact renewal_memory_sum_bound μ n (fun t => n-t)
      · rw [Fin.sum_univ_eq_sum_range (fun t => oneStepRisk A μ (n+1) (t+1))]
        exact suffix_query_KL_budget A μ n
    _ = _ := by ring

theorem predict_interior (n : ℕ) (hn : 0 < n) (x : List Bool) (hx : x.length = n) :
    0 < (predict A n x : ℝ) ∧ (predict A n x : ℝ) < 1 := by
  let w : Word n := ⟨x, hx⟩
  have hp := averageKernel_pos A n hn w true
  have hf := averageKernel_pos A n hn w false
  have ht := (averageKernel A n hn w).total
  simp only [Fintype.sum_bool] at ht
  rw [averageKernel_true A] at hp ht
  exact ⟨hp, by linarith⟩

theorem averageKernel_binary (n : ℕ) (hn : 0 < n) (x : Word n) :
    averageKernel A n hn x = binary (predict A n x.val : ℝ)
      (predict_interior A n hn x.val x.property).1.le
      (predict_interior A n hn x.val x.property).2.le := by
  apply Distribution.ext
  intro b
  have ht := (averageKernel A n hn x).total
  simp only [Fintype.sum_bool] at ht
  cases b
  · rw [binary_false]
    rw [averageKernel_true A] at ht
    linarith
  · exact averageKernel_true A n hn x

lemma average_loss_eq (μ : Law) (n : ℕ) (hn : 0 < n) (x : Word n) :
    Distribution.kl (next μ x.val) (averageKernel A n hn x) =
      Boundary.klReal (conditional μ x.val) (predict A n x.val : ℝ) := by
  rw [averageKernel_binary A]
  exact binary_klReal (conditional_mem_unitInterval μ x.val).1
    (conditional_mem_unitInterval μ x.val).2
    (predict_interior A n hn x.val x.property).1 (predict_interior A n hn x.val x.property).2

lemma implemented_loss_nonneg (μ : Law) (n : ℕ) (hn : 0 < n)
    (x : List Bool) (hx : x.length = n) :
    0 ≤ Boundary.klReal (conditional μ x) (predict A n x : ℝ) := by
  rw [← average_loss_eq A μ n hn ⟨x, hx⟩]
  exact kl_nonneg _ _ (fun b _ => averageKernel_pos A n hn ⟨x, hx⟩ b)

noncomputable def sourcePredictor (n : ℕ) (hn : 0 < n) : RandomizedPredictor := fun x =>
  if hx : x.length = n then
    ⟨MeasureTheory.Measure.dirac ⟨(predict A n x : ℝ),
      ⟨(predict_interior A n hn x hx).1.le, (predict_interior A n hn x hx).2.le⟩⟩,
      MeasureTheory.Measure.dirac.isProbabilityMeasure⟩
  else ⟨MeasureTheory.Measure.dirac ⟨1/2, by norm_num⟩,
    MeasureTheory.Measure.dirac.isProbabilityMeasure⟩

theorem source_risk_eq (μ : Law) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor A n hn) μ = ENNReal.ofReal
      (∑ x : Word n, blockMass μ x.val *
        Distribution.kl (next μ x.val) (averageKernel A n hn x)) := by
  unfold risk
  calc
    _ = ∑ x ∈ (words n).toFinset, ENNReal.ofReal
        (blockMass μ x * Boundary.klReal (conditional μ x) (predict A n x : ℝ)) := by
      apply sum_congr rfl
      intro x hx
      have hlen : x.length = n := (mem_words n x).mp (List.mem_toFinset.mp hx)
      have hi := predict_interior A n hn x hlen
      simp only [sourcePredictor, hlen, ↓reduceDIte, MeasureTheory.ProbabilityMeasure.toMeasure,
        MeasureTheory.lintegral_dirac]
      rw [Boundary.kl, if_neg (by simp [hi.1.ne', ne_of_lt hi.2])]
      exact (ENNReal.ofReal_mul (blockMass_nonneg μ x)).symm
    _ = ENNReal.ofReal (∑ x ∈ (words n).toFinset,
        blockMass μ x * Boundary.klReal (conditional μ x) (predict A n x : ℝ)) := by
      exact (ENNReal.ofReal_sum_of_nonneg (fun x hx => mul_nonneg (blockMass_nonneg μ x)
        (implemented_loss_nonneg A μ n hn x ((mem_words n x).mp (List.mem_toFinset.mp hx))))).symm
    _ = _ := by
      congr 1
      simp_rw [average_loss_eq A]
      rw [sum_word n (fun x => blockMass μ x * Boundary.klReal (conditional μ x) (predict A n x : ℝ))]
      exact List.sum_toFinset _ (words_nodup n)

theorem compression_prediction (μ : Law) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor A n hn) μ ≤
      ENNReal.ofReal ((blockKL A μ (n+1) + Real.log (n+2)) / n) := by
  rw [source_risk_eq A]
  exact ENNReal.ofReal_le_ofReal (compression_prediction_real A μ n hn)

theorem blockKL_eq_source_sum (μ : Law) (N : ℕ) :
    blockKL A μ N = ∑ x ∈ (words N).toFinset,
      blockMass μ x * Real.log (blockMass μ x / (A.mass x : ℝ)) := by
  unfold blockKL Distribution.kl
  simp only [blockDistribution_apply, assignmentDistribution_apply A]
  calc
    _ = ∑ x : Word N, blockMass μ x.val *
        Real.log (blockMass μ x.val / (A.mass x.val : ℝ)) := by
      apply sum_congr rfl
      intro x _
      by_cases hp : blockMass μ x.val = 0
      · simp [hp]
      · rw [Real.log_div hp (by exact_mod_cast (A.positive x.val).ne')]
    _ = _ := by
      rw [sum_word N (fun x => blockMass μ x * Real.log (blockMass μ x / (A.mass x : ℝ)))]
      exact (List.sum_toFinset _ (words_nodup N)).symm

/-- Any separately proved block redundancy estimate transfers to actual stationary risk. -/
theorem source_risk_le_of_block_regret (μ : Law) (n : ℕ) (hn : 0 < n) (B : ℝ)
    (hB : (∑ x ∈ (words (n+1)).toFinset, blockMass μ x *
      Real.log (blockMass μ x / (A.mass x : ℝ))) ≤ B) :
    risk n (sourcePredictor A n hn) μ ≤ ENNReal.ofReal ((B + Real.log (n+2)) / n) := by
  apply (compression_prediction A μ n hn).trans
  apply ENNReal.ofReal_le_ofReal
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg n)
  apply add_le_add_right
  rw [blockKL_eq_source_sum A]
  exact hB

end Paper37.GenericCompressionPrediction
