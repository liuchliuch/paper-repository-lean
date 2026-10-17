import Paper37.GenericCompressionPrediction

/-! The universal, arbitrary-stationary-binary-process part of Lemma D.2.
A process is represented by its genuine cylinder probabilities. Positivity,
normalization at the empty word, right consistency, and stationary left
consistency are the complete finite-dimensional probability requirements;
no KL estimate or memory bound is a field. Assignments here have real masses.
-/
namespace Paper37.StationaryCompression

open scoped ENNReal

open Finset Compression Compression.Distribution RenewalCompression
open CompressionPrediction Prediction

/-- Consistent cylinder probabilities of a stationary binary process. -/
structure StationaryBinaryLaw where
  mass : List Bool → ℝ
  nonneg : ∀ x, 0 ≤ mass x
  empty : mass [] = 1
  right : ∀ x, mass x = mass (x ++ [false]) + mass (x ++ [true])
  left : ∀ x, mass x = mass (false :: x) + mass (true :: x)

noncomputable def blockMass (P : StationaryBinaryLaw) (x : List Bool) : ℝ := P.mass x

lemma blockMass_nonneg (P : StationaryBinaryLaw) (x : List Bool) : 0 ≤ blockMass P x := P.nonneg x

lemma blockMass_right_consistency (P : StationaryBinaryLaw) (x : List Bool) :
    blockMass P x = blockMass P (x ++ [false]) + blockMass P (x ++ [true]) := P.right x

lemma blockMass_left_consistency (P : StationaryBinaryLaw) (x : List Bool) :
    blockMass P x = blockMass P (false :: x) + blockMass P (true :: x) := P.left x

lemma blockMass_normalized (P : StationaryBinaryLaw) (n : ℕ) :
    Renewal.wordSum n (blockMass P) = 1 := by
  induction n with
  | zero => simpa only [Renewal.wordSum_zero] using P.empty
  | succ n ih =>
    rw [Renewal.wordSum_step, ← wordSum_add]
    simp_rw [← blockMass_left_consistency]
    exact ih

noncomputable def conditional (P : StationaryBinaryLaw) (x : List Bool) : ℝ :=
  blockMass P (x ++ [true]) / blockMass P x

lemma conditional_mem_unitInterval (P : StationaryBinaryLaw) (x : List Bool) :
    0 ≤ conditional P x ∧ conditional P x ≤ 1 := by
  constructor
  · exact div_nonneg (blockMass_nonneg P _) (blockMass_nonneg P _)
  · unfold conditional
    by_cases h : blockMass P x = 0
    · simp [h]
    · have hp : 0 < blockMass P x := lt_of_le_of_ne (blockMass_nonneg P _) (Ne.symm h)
      apply (div_le_one hp).mpr
      have h := blockMass_right_consistency P x
      linarith [blockMass_nonneg P (x ++ [false])]

open Renewal (words wordSum wordSum_step mem_words words_nodup)

theorem stationary_left_marginal (μ : StationaryBinaryLaw) (k : ℕ) (s : List Bool) :
    wordSum k (fun o => blockMass μ (o ++ s)) = blockMass μ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [wordSum_step, ← wordSum_add]
    simp only [List.cons_append]
    simp_rw [← blockMass_left_consistency]
    exact ih

theorem stationary_suffix_marginal (μ : StationaryBinaryLaw) (k : ℕ) (s : List Bool) :
    (∑ o : Word k, blockMass μ (o.val ++ s)) = blockMass μ s := by
  exact (sum_word k (fun o => blockMass μ (o ++ s))).trans (stationary_left_marginal μ k s)

noncomputable def blockDistribution (μ : StationaryBinaryLaw) (n : ℕ) : Distribution (Word n) where
  mass x := blockMass μ x.val
  nonneg x := blockMass_nonneg μ x.val
  total := by rw [sum_word]; exact blockMass_normalized μ n

@[simp] lemma blockDistribution_apply (μ : StationaryBinaryLaw) (n : ℕ) (x : Word n) :
    blockDistribution μ n x = blockMass μ x.val := rfl

noncomputable def next (μ : StationaryBinaryLaw) (x : List Bool) : Distribution Bool :=
  binary (conditional μ x) (conditional_mem_unitInterval μ x).1
    (conditional_mem_unitInterval μ x).2

@[simp] lemma next_true (μ : StationaryBinaryLaw) (x : List Bool) : next μ x true = conditional μ x := rfl

@[simp] lemma next_false (μ : StationaryBinaryLaw) (x : List Bool) : next μ x false = 1 - conditional μ x := rfl

theorem weighted_next (μ : StationaryBinaryLaw) (x : List Bool) (b : Bool) :
    blockMass μ x * next μ x b = blockMass μ (x ++ [b]) := by
  have ht : blockMass μ x * conditional μ x = blockMass μ (x ++ [true]) := by
    by_cases hx : blockMass μ x = 0
    · have hc := blockMass_right_consistency μ x
      have hz : blockMass μ (x ++ [true]) = 0 :=
        le_antisymm (by linarith [blockMass_nonneg μ (x ++ [false])])
          (blockMass_nonneg μ (x ++ [true]))
      simp [hx, hz]
    · exact mul_div_cancel₀ _ hx
  cases b
  · rw [next_false]
    have hc := blockMass_right_consistency μ x
    nlinarith
  · exact ht

lemma older_component_le (μ : StationaryBinaryLaw) (k : ℕ) (s : List Bool) (o : Word k) :
    blockMass μ (o.val ++ s) ≤ blockMass μ s := by
  rw [← stationary_suffix_marginal μ k s]
  exact single_le_sum (fun j _ => blockMass_nonneg μ (j.val ++ s)) (mem_univ o)

noncomputable def olderPosterior (μ : StationaryBinaryLaw) (k : ℕ) (s : List Bool) : Distribution (Word k) := by
  classical
  exact {
    mass := fun o => if 0 < blockMass μ s then blockMass μ (o.val ++ s) / blockMass μ s
      else blockDistribution μ k o
    nonneg := fun o => by
      split_ifs
      · exact div_nonneg (blockMass_nonneg μ _) (blockMass_nonneg μ _)
      · exact (blockDistribution μ k).nonneg o
    total := by
      split_ifs with h
      · simp only [div_eq_mul_inv]
        rw [← sum_mul, stationary_suffix_marginal]
        exact mul_inv_cancel₀ h.ne'
      · exact (blockDistribution μ k).total }

theorem olderPosterior_bayes (μ : StationaryBinaryLaw) (k : ℕ) (s : List Bool) (o : Word k) :
    blockMass μ s * olderPosterior μ k s o = blockMass μ (o.val ++ s) := by
  classical
  by_cases h : 0 < blockMass μ s
  · simp only [olderPosterior, h, ↓reduceIte]
    exact mul_div_cancel₀ _ h.ne'
  · have hs : blockMass μ s = 0 := le_antisymm (le_of_not_gt h) (blockMass_nonneg μ s)
    have ho : blockMass μ (o.val ++ s) = 0 :=
      le_antisymm (hs ▸ older_component_le μ k s o) (blockMass_nonneg μ _)
    rw [hs, zero_mul, ho]

theorem stationary_suffix_next (μ : StationaryBinaryLaw) (k : ℕ) (s : List Bool) (b : Bool) :
    (∑ o : Word k, blockMass μ (o.val ++ s) * next μ (o.val ++ s) b) =
      blockMass μ s * next μ s b := by
  simp_rw [weighted_next]
  simp only [List.append_assoc]
  exact stationary_suffix_marginal μ k (s ++ [b])

theorem mixture_next_eq (μ : StationaryBinaryLaw) (k : ℕ) (s : List Bool) (hs : 0 < blockMass μ s) :
    mixture (olderPosterior μ k s) (fun o => next μ (o.val ++ s)) = next μ s := by
  apply Distribution.ext
  intro b
  apply (mul_left_cancel₀ hs.ne')
  simp only [mixture_apply, mul_sum]
  simp_rw [← mul_assoc, olderPosterior_bayes]
  exact stationary_suffix_next μ k s b

noncomputable def memory (μ : StationaryBinaryLaw) (k t : ℕ) : ℝ :=
  ∑ s : Word t, blockMass μ s.val * mutualInformation (olderPosterior μ k s.val)
    (fun o => next μ (o.val ++ s.val))

noncomputable def suffixRisk (μ : StationaryBinaryLaw) (k t : ℕ) (q : Word t → Distribution Bool) : ℝ :=
  ∑ s : Word t, ∑ o : Word k, blockMass μ (o.val ++ s.val) *
    Distribution.kl (next μ (o.val ++ s.val)) (q s)

theorem suffixRisk_decomposition (μ : StationaryBinaryLaw) (k t : ℕ) (q : Word t → Distribution Bool) :
    suffixRisk μ k t q = memory μ k t +
      ∑ s : Word t, blockMass μ s.val * Distribution.kl (next μ s.val) (q s) := by
  unfold suffixRisk memory
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro s _
  calc
    _ = blockMass μ s.val * conditionalKL (olderPosterior μ k s.val)
        (fun o => next μ (o.val ++ s.val)) (q s) := by
      unfold conditionalKL
      rw [mul_sum]
      apply sum_congr rfl
      intro o _
      rw [← mul_assoc, olderPosterior_bayes]
    _ = _ := by
      rw [conditionalKL_decomposition, mul_add]
      by_cases hs : 0 < blockMass μ s.val
      · rw [mixture_next_eq μ k s.val hs]
      · have hz : blockMass μ s.val = 0 :=
          le_antisymm (le_of_not_gt hs) (blockMass_nonneg μ s.val)
        simp [hz]


noncomputable def risk (n : ℕ) (q : RandomizedPredictor) (P : StationaryBinaryLaw) : ℝ≥0∞ :=
  ∑ x ∈ (words n).toFinset, ENNReal.ofReal (blockMass P x) *
    ∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl (conditional P x) r.val ∂(q x).toMeasure

structure Assignment where
  mass : List Bool → ℝ
  positive : ∀ x, 0 < mass x
  normalized : ∀ N, (∑ x ∈ (words N).toFinset, mass x) = 1

variable (A : Assignment)

noncomputable def prefixMass (N : ℕ) (z : List Bool) : ℝ :=
  ∑ v ∈ (words (N-z.length)).toFinset, A.mass (z ++ v)

noncomputable def blockConditional (N : ℕ) (z : List Bool) : ℝ :=
  prefixMass A N (z ++ [true]) / prefixMass A N z

noncomputable def predict (n : ℕ) (x : List Bool) : ℝ :=
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

noncomputable def oneStepRisk (μ : StationaryBinaryLaw) (N t : ℕ) : ℝ :=
  ∑ x : Word t, blockMass μ x.val * Distribution.kl (next μ x.val) (kernel A N x.val)

noncomputable def blockKL (μ : StationaryBinaryLaw) (N : ℕ) : ℝ :=
  Distribution.kl (blockDistribution μ N) (assignmentDistribution A N)

theorem prefixKL_step (μ : StationaryBinaryLaw) (N t : ℕ) (ht : t < N) :
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

theorem sum_oneStepRisk (μ : StationaryBinaryLaw) (N K : ℕ) (hK : K ≤ N) :
    (∑ t ∈ range K, oneStepRisk A μ N t) =
      Distribution.kl (blockDistribution μ K) (prefixDistribution A N K hK) := by
  induction K with
  | zero =>
    unfold Distribution.kl
    simp only [blockDistribution_apply, prefixDistribution_apply A]
    rw [sum_word 0 (fun z => blockMass μ z *
      (Real.log (blockMass μ z) - Real.log (prefixMass A N z : ℝ)))]
    simp [blockMass, μ.empty]
  | succ K ih =>
    rw [sum_range_succ, ih (by omega), prefixKL_step A μ N K (by omega)]

lemma oneStepRisk_nonneg (μ : StationaryBinaryLaw) (N t : ℕ) : 0 ≤ oneStepRisk A μ N t := by
  apply sum_nonneg
  intro x _
  exact mul_nonneg (blockMass_nonneg μ x.val)
    (kl_nonneg _ _ (fun b _ => kernel_pos A N x.val b))

theorem suffix_query_KL_budget (μ : StationaryBinaryLaw) (n : ℕ) :
    (∑ t ∈ range n, oneStepRisk A μ (n+1) (t+1)) ≤ blockKL A μ (n+1) := by
  have h := sum_oneStepRisk A μ (n+1) (n+1) le_rfl
  rw [sum_range_succ'] at h
  unfold blockKL assignmentDistribution
  rw [← h]
  exact le_add_of_nonneg_right (oneStepRisk_nonneg A μ (n+1) 0)

theorem full_suffixRisk_eq (μ : StationaryBinaryLaw) (n t : ℕ) (ht : t ≤ n)
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


theorem full_suffixRisk_decomposition (μ : StationaryBinaryLaw) (N n t : ℕ) (ht : t ≤ n) :
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

theorem compression_prediction_real (μ : StationaryBinaryLaw) (n : ℕ) (hn : 0 < n) :
    (∑ x : Word n, blockMass μ x.val *
      Distribution.kl (next μ x.val) (averageKernel A n hn x)) ≤
      (blockKL A μ (n+1) + (∑ t ∈ range n, memory μ (n-(t+1)) (t+1))) / n := by
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
    _ ≤ (n : ℝ)⁻¹ * ((∑ t ∈ range n, memory μ (n-(t+1)) (t+1)) + blockKL A μ (n+1)) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg n))
      apply add_le_add
      · rw [Fin.sum_univ_eq_sum_range (fun t => memory μ (n-(t+1)) (t+1))]
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

lemma average_loss_eq (μ : StationaryBinaryLaw) (n : ℕ) (hn : 0 < n) (x : Word n) :
    Distribution.kl (next μ x.val) (averageKernel A n hn x) =
      Boundary.klReal (conditional μ x.val) (predict A n x.val : ℝ) := by
  rw [averageKernel_binary A]
  exact binary_klReal (conditional_mem_unitInterval μ x.val).1
    (conditional_mem_unitInterval μ x.val).2
    (predict_interior A n hn x.val x.property).1 (predict_interior A n hn x.val x.property).2

lemma implemented_loss_nonneg (μ : StationaryBinaryLaw) (n : ℕ) (hn : 0 < n)
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

theorem source_risk_eq (μ : StationaryBinaryLaw) (n : ℕ) (hn : 0 < n) :
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

theorem compression_prediction (μ : StationaryBinaryLaw) (n : ℕ) (hn : 0 < n) :
    risk n (sourcePredictor A n hn) μ ≤
      ENNReal.ofReal ((blockKL A μ (n+1) + (∑ t ∈ range n, memory μ (n-(t+1)) (t+1))) / n) := by
  rw [source_risk_eq A]
  exact ENNReal.ofReal_le_ofReal (compression_prediction_real A μ n hn)

theorem blockKL_eq_source_sum (μ : StationaryBinaryLaw) (N : ℕ) :
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



/-- Every genuine renewal law supplies the cylinder-law representation directly. -/
noncomputable def ofRenewal (μ : Renewal.Law) : StationaryBinaryLaw where
  mass := Renewal.blockMass μ
  nonneg := Renewal.blockMass_nonneg μ
  empty := by simp [Renewal.blockMass, Renewal.stationaryNumerator, Renewal.residual_zero,
    div_self (Renewal.mean_pos μ).ne']
  right := Renewal.blockMass_right_consistency μ
  left := Renewal.blockMass_left_consistency μ

lemma sum_word_finset (n : ℕ) (f : List Bool → ℝ) :
    (∑ x : Word n, f x.val) = ∑ x ∈ (words n).toFinset, f x := by
  rw [sum_word]
  exact (List.sum_toFinset _ (words_nodup n)).symm

lemma uniform_wordSum (n : ℕ) :
    wordSum n (fun x => (1/2 : ℝ)^x.length) = 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [wordSum_step]
    simp only [List.length_cons, pow_succ']
    simp_rw [Renewal.wordSum_mul, ih]
    norm_num

/-- A single arbitrary real full-support Q_N extends to an assignment family by
using fair coins at every other length. This removes any extra family hypothesis
from the source's quantifier over block assignments. -/
noncomputable def extendAssignment (N : ℕ) (Q : Distribution (Word N))
    (hQ : ∀ x, 0 < Q x) : Assignment where
  mass x := if hx : x.length = N then Q ⟨x, hx⟩ else (1/2 : ℝ)^x.length
  positive x := by
    split_ifs
    · exact hQ _
    · exact pow_pos (by norm_num) _
  normalized K := by
    let f := fun x : List Bool => if hx : x.length = N then Q ⟨x, hx⟩ else (1/2 : ℝ)^x.length
    change (∑ x ∈ (words K).toFinset, f x) = 1
    rw [← sum_word_finset K f]
    by_cases hK : K = N
    · subst K
      have heq : (∑ x : Word N, f x.val) = ∑ x : Word N, Q x := by
        apply sum_congr rfl
        intro x _
        simp only [f, x.property, ↓reduceDIte]
        congr 1
      rw [heq]
      exact Q.total
    · have heq : (∑ x : Word K, f x.val) = ∑ x : Word K, (1/2 : ℝ)^x.val.length := by
        apply sum_congr rfl
        intro x _
        simp [f, x.property, hK]
      rw [heq, sum_word K (fun x => (1/2 : ℝ)^x.length)]
      exact uniform_wordSum K

/-- The extended family retains the supplied block distribution exactly. -/
theorem assignmentDistribution_extend (N : ℕ) (Q : Distribution (Word N))
    (hQ : ∀ x, 0 < Q x) : assignmentDistribution (extendAssignment N Q hQ) N = Q := by
  apply Distribution.ext
  intro x
  rw [assignmentDistribution_apply]
  simp only [extendAssignment, x.property, ↓reduceDIte]
  congr 1

/-- Original universal Lemma D.2: every stationary binary cylinder law and every
single real full-support assignment Q_(n+1). The predictor is exactly the average
of the Q-prefix conditionals on the observed suffixes; memory is its actual
conditional mutual information under the process, computed by Bayes' rule. -/
theorem compression_to_prediction_single (P : StationaryBinaryLaw) (n : ℕ) (hn : 0 < n)
    (Q : Distribution (Word (n+1))) (hQ : ∀ x, 0 < Q x) :
    risk n (sourcePredictor (extendAssignment (n+1) Q hQ) n hn) P ≤ ENNReal.ofReal
      ((Distribution.kl (blockDistribution P (n+1)) Q +
        (∑ t ∈ range n, memory P (n-(t+1)) (t+1))) / n) := by
  have h := compression_prediction (extendAssignment (n+1) Q hQ) P n hn
  unfold blockKL at h
  rw [assignmentDistribution_extend] at h
  exact h

end Paper37.StationaryCompression
