import Paper02.SparseRecovery
import Paper02.HashSampling
import Paper02.WeightEval
import Paper02.ChecksumFailure

/-!
# The actual multilevel turnstile summary

The state update below reads one integer coordinate update at a time and stores
only residues modulo `q`. The final-vector invariant has no restriction on the
length of the stream or on any intermediate frequency. The candidate decoder
is the seed-independent mathematical specification from `SparseRecovery`;
its connection with the bounded-workspace Hankel implementation is separate.
-/

noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Paper02.Streaming

open SparseRecovery Hashing Sampling

abbrev CopySeed (J ℓ q : ℕ) := Hashing.Seed J ℓ × (Fin (J + 1) → ZMod q)
abbrev CopyState (J K q : ℕ) := Fin (J + 1) → Summary K (ZMod q)

/-- True sampled frequencies; this is used only in the correctness statement. -/
def sampledVector {d J ℓ : ℕ} (h : Hashing.Seed J ℓ) (j : ℕ)
    (v : Fin d → ℤ) : Fin d → ℤ := fun i =>
  if PrefixZero j (Hashing.hash (binaryVector ℓ i.val) h) then v i else 0

lemma sampledVector_zero {d J ℓ : ℕ} (h : Hashing.Seed J ℓ) (j : ℕ) :
    sampledVector h j (0 : Fin d → ℤ) = 0 := by
  funext i
  simp [sampledVector]

lemma sampledVector_update {d J ℓ : ℕ} (h : Hashing.Seed J ℓ) (j : ℕ)
    (v : Fin d → ℤ) (i : Fin d) (a : ℤ) :
    sampledVector h j (v + Pi.single i a) =
      if PrefixZero j (Hashing.hash (binaryVector ℓ i.val) h) then
        sampledVector h j v + Pi.single i a else sampledVector h j v := by
  funext k
  by_cases hk : k = i
  · subst k
    split_ifs <;> simp_all [sampledVector]
  · split_ifs <;> simp_all [sampledVector, Pi.add_apply, Pi.single_eq_of_ne hk]

/-- The stored summary of every sampled final vector. -/
def finalSummary {d J ℓ q : ℕ} [Fact q.Prime] (K : ℕ)
    (seed : CopySeed J ℓ q) (v : Fin d → ℤ) : CopyState J K q :=
  fun j => integerSummary K (seed.2 j) (sampledVector seed.1 j.val v)

/-- The actual streaming transition. Each field accumulator is reduced after
an update; the integer update itself is read-only input. -/
def update {d J ℓ q : ℕ} [Fact q.Prime] (K : ℕ)
    (seed : CopySeed J ℓ q) (s : CopyState J K q) (u : Update d) : CopyState J K q :=
  fun j => if PrefixZero j.val (Hashing.hash (binaryVector ℓ u.1.val) seed.1) then
    updateSummary K (seed.2 j) (s j) u.1 (u.2 : ZMod q) else s j

lemma finalSummary_zero {d J ℓ q : ℕ} [Fact q.Prime] (K : ℕ)
    (seed : CopySeed J ℓ q) : finalSummary (d := d) K seed 0 = 0 := by
  funext j
  simp [finalSummary, sampledVector_zero, integerSummary_zero]

lemma update_finalSummary {d J ℓ q : ℕ} [Fact q.Prime] (K : ℕ)
    (seed : CopySeed J ℓ q) (v : Fin d → ℤ) (u : Update d) :
    update K seed (finalSummary K seed v) u =
      finalSummary K seed (v + Pi.single u.1 u.2) := by
  funext j
  simp only [update, finalSummary, sampledVector_update]
  split_ifs
  · exact (integerSummary_update K (seed.2 j) _ u.1 u.2).symm
  · rfl

/-- A single pass over the update list. -/
def run {d J ℓ q : ℕ} [Fact q.Prime] (K : ℕ) (seed : CopySeed J ℓ q)
    (stream : List (Update d)) : CopyState J K q := stream.foldl (update K seed) 0

/-- No intermediate-frequency premise is needed for the complete online
summary invariant. -/
theorem run_finalVector {d J ℓ q : ℕ} [Fact q.Prime] (K : ℕ)
    (seed : CopySeed J ℓ q) (stream : List (Update d)) :
    run K seed stream = finalSummary K seed (finalVector stream) := by
  have aux : ∀ (xs : List (Update d)) (v : Fin d → ℤ),
      xs.foldl (update K seed) (finalSummary K seed v) =
        finalSummary K seed (xs.foldl (fun w u => w + Pi.single u.1 u.2) v) := by
    intro xs
    induction xs with
    | nil => intro v; rfl
    | cons u us ih =>
      intro v
      simp only [List.foldl_cons]
      rw [update_finalSummary]
      exact ih _
  simpa only [run, finalVector, finalSummary_zero] using aux stream 0

/-- Decode one level, using that level's independently stored checksum seed. -/
def decodedAt {d J ℓ q : ℕ} [Fact q.Prime] (U K : ℕ)
    (seed : CopySeed J ℓ q) (s : CopyState J K q) (j : Fin (J + 1)) : Option (Fin d → ℤ) :=
  decodeSummary U K (seed.2 j) (s j)

def acceptedLevels {d J ℓ q : ℕ} [Fact q.Prime] (U K : ℕ)
    (seed : CopySeed J ℓ q) (s : CopyState J K q) : Finset (Fin (J + 1)) :=
  Finset.univ.filter (fun j => decodedAt (d := d) U K seed s j ≠ none)

/-- Choose the least successfully decoded level, or zero if all levels fail. -/
def selectedLevel {d J ℓ q : ℕ} [Fact q.Prime] (U K : ℕ)
    (seed : CopySeed J ℓ q) (s : CopyState J K q) : Fin (J + 1) :=
  if h : (acceptedLevels (d := d) U K seed s).Nonempty then
    (acceptedLevels (d := d) U K seed s).min' h else 0

lemma selectedLevel_le {d J ℓ q U K : ℕ} [Fact q.Prime]
    (seed : CopySeed J ℓ q) (s : CopyState J K q) (j : Fin (J + 1))
    (hj : decodedAt (d := d) U K seed s j ≠ none) :
    selectedLevel (d := d) U K seed s ≤ j ∧
      decodedAt (d := d) U K seed s (selectedLevel (d := d) U K seed s) ≠ none := by
  have hm : j ∈ acceptedLevels (d := d) U K seed s := by simp [acceptedLevels, hj]
  have hn : (acceptedLevels (d := d) U K seed s).Nonempty := ⟨j, hm⟩
  simp only [selectedLevel, dif_pos hn]
  exact ⟨Finset.min'_le _ j hm,
    (Finset.mem_filter.mp (Finset.min'_mem _ hn)).2⟩

/-- The moment to be estimated. -/
def moment {d : ℕ} (w : ℤ → ℝ) (v : Fin d → ℤ) : ℝ := ∑ i, w (v i)

/-- The paper's output: inverse retention probability times recovered weight. -/
def output {d J ℓ q : ℕ} [Fact q.Prime] (w : ℤ → ℝ) (U K : ℕ)
    (seed : CopySeed J ℓ q) (s : CopyState J K q) : ℝ :=
  let j := selectedLevel (d := d) U K seed s
  match decodedAt (d := d) U K seed s j with
  | none => 0
  | some v => (2 : ℝ) ^ j.val * moment w v

/-- Bad recovery means a genuinely dense sample was accepted. -/
def recoveryFailure {d J ℓ q : ℕ} [Fact q.Prime] (U K : ℕ)
    (v : Fin d → ℤ) : Set (CopySeed J ℓ q) :=
  {seed | ∃ j : Fin (J + 1), K < (integerSupport (sampledVector seed.1 j.val v)).card ∧
    decodedAt (d := d) U K seed (finalSummary K seed v) j ≠ none}

lemma sampledVector_bounded {d J ℓ U : ℕ} (h : Hashing.Seed J ℓ) (j : ℕ)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U) :
    ∀ i, -(U : ℤ) ≤ sampledVector h j v i ∧ sampledVector h j v i ≤ U := by
  intro i
  dsimp [sampledVector]
  split_ifs
  · exact hv i
  · constructor <;> omega

lemma decodedAt_sparse {d J ℓ q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) (seed : CopySeed J ℓ q)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (j : Fin (J + 1)) (hj : (integerSupport (sampledVector seed.1 j.val v)).card ≤ K) :
    decodedAt (d := d) U K seed (finalSummary K seed v) j = some (sampledVector seed.1 j.val v) := by
  exact decodeSummary_sparse hdq hUq _ (sampledVector_bounded seed.1 j.val v hv) hj (seed.2 j)

lemma decodedAt_of_no_failure {d J ℓ q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) (seed : CopySeed J ℓ q)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hseed : seed ∉ recoveryFailure U K v) (j : Fin (J + 1))
    (hj : decodedAt (d := d) U K seed (finalSummary K seed v) j ≠ none) :
    decodedAt (d := d) U K seed (finalSummary K seed v) j = some (sampledVector seed.1 j.val v) := by
  by_cases hs : (integerSupport (sampledVector seed.1 j.val v)).card ≤ K
  · exact decodedAt_sparse hdq hUq seed v hv j hs
  · exact False.elim (hseed ⟨j, Nat.lt_of_not_ge hs, hj⟩)

lemma selectedLevel_sparse_le {d J ℓ q U K : ℕ} [Fact q.Prime]
    (hdq : d < q) (hUq : 2 * U < q) (seed : CopySeed J ℓ q)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (j : Fin (J + 1)) (hj : (integerSupport (sampledVector seed.1 j.val v)).card ≤ K) :
    selectedLevel (d := d) U K seed (finalSummary K seed v) ≤ j := by
  exact (selectedLevel_le seed _ j (by rw [decodedAt_sparse hdq hUq seed v hv j hj]; simp)).1

lemma output_of_no_failure {d J ℓ q U K : ℕ} [Fact q.Prime]
    (w : ℤ → ℝ) (hdq : d < q) (hUq : 2 * U < q) (seed : CopySeed J ℓ q)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hseed : seed ∉ recoveryFailure U K v) (j : Fin (J + 1))
    (hj : (integerSupport (sampledVector seed.1 j.val v)).card ≤ K) :
    output (d := d) w U K seed (finalSummary K seed v) =
      (2 : ℝ) ^ (selectedLevel (d := d) U K seed (finalSummary K seed v)).val *
        moment w (sampledVector seed.1
          (selectedLevel (d := d) U K seed (finalSummary K seed v)).val v) := by
  have ha := (selectedLevel_le seed _ j
    (by rw [decodedAt_sparse hdq hUq seed v hv j hj]; simp)).2
  have hc := decodedAt_of_no_failure hdq hUq seed v hv hseed _ ha
  simp only [output, hc]

/-- Level zero always retains every coordinate. -/
lemma sampledVector_level_zero {d J ℓ : ℕ} (h : Hashing.Seed J ℓ) (v : Fin d → ℤ) :
    sampledVector h 0 v = v := by
  funext i
  simp [sampledVector, PrefixZero]

/-- Exact recovery on sparse final vectors, including the zero vector. -/
theorem output_sparse_exact {d J ℓ q U K : ℕ} [Fact q.Prime]
    (w : ℤ → ℝ) (hdq : d < q) (hUq : 2 * U < q) (seed : CopySeed J ℓ q)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hs : (integerSupport v).card ≤ K) :
    output (d := d) w U K seed (finalSummary K seed v) = moment w v := by
  have hc : decodedAt (d := d) U K seed (finalSummary K seed v) 0 = some v := by
    simpa only [Fin.val_zero, sampledVector_level_zero] using
      decodedAt_sparse hdq hUq seed v hv 0 (by simpa [sampledVector_level_zero] using hs)
  have hl : selectedLevel (d := d) U K seed (finalSummary K seed v) = 0 := by
    have hle := (selectedLevel_le seed _ 0 (by rw [hc]; simp)).1
    exact le_antisymm hle (Fin.zero_le _)
  simp [output, hl, hc]


/-- Only nonzero final coordinates enter the concentration calculation. -/
abbrev Active {d : ℕ} (v : Fin d → ℤ) := {i : Fin d // v i ≠ 0}

lemma card_active {d : ℕ} (v : Fin d → ℤ) :
    Fintype.card (Active v) = (integerSupport v).card := by
  simp [Active, Fintype.card_subtype, integerSupport]

lemma sum_active {d : ℕ} (v : Fin d → ℤ) (g : Fin d → ℝ)
    (hg : ∀ i, v i = 0 → g i = 0) : (∑ i, g i) = ∑ i : Active v, g i.val := by
  rw [← Finset.sum_subtype (integerSupport v) (by simp [integerSupport]) g]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro i _ hi
  have hz : v i = 0 := by simpa [integerSupport] using hi
  exact hg i hz

lemma moment_active {d : ℕ} (w : ℤ → ℝ) (hw : w 0 = 0) (v : Fin d → ℤ) :
    moment w v = ∑ i : Active v, w (v i.val) :=
  sum_active v _ (by intro i hi; simp [hi, hw])

/-- The actual short-seed indicators restricted to the final support. -/
def activeIndicator {d J ℓ q : ℕ} (v : Fin d → ℤ) (j : ℕ)
    (i : Active v) (seed : CopySeed J ℓ q) : ℝ := retained j i.val seed.1

lemma activeIndicator_pairwise {d J ℓ q : ℕ} (v : Fin d → ℤ)
    (hd : d ≤ 2 ^ ℓ) {j : ℕ} (hj : j ≤ J) [NeZero q] :
    PairwiseBernoulli (FiniteLaw.uniform (CopySeed J ℓ q))
      (activeIndicator v j) (dyadicProb j) where
  zero_or_one i seed := (retained_pairwise_extra_seed hd hj (Fin (J + 1) → ZMod q)).zero_or_one i.val seed
  mean i := (retained_pairwise_extra_seed hd hj (Fin (J + 1) → ZMod q)).mean i.val
  mixed i k hik := (retained_pairwise_extra_seed hd hj (Fin (J + 1) → ZMod q)).mixed
    i.val k.val (fun h => hik (Subtype.ext h))

lemma moment_sampled {d J ℓ q : ℕ} (w : ℤ → ℝ) (hw : w 0 = 0)
    (v : Fin d → ℤ) (seed : CopySeed J ℓ q) (j : ℕ) :
    moment w (sampledVector seed.1 j v) =
      ∑ i : Active v, activeIndicator v j i seed * w (v i.val) := by
  unfold moment
  rw [sum_active v _ (by
    intro i hi
    simp [sampledVector, hi, hw])]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [sampledVector, activeIndicator, retained]
  split_ifs <;> simp [hw]

lemma supportWeight_moment {d : ℕ} (v : Fin d → ℤ) :
    moment (fun k => if k = 0 then (0 : ℝ) else 1) v =
      ((integerSupport v).card : ℝ) := by
  unfold moment integerSupport
  rw [Finset.card_filter]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp_all

lemma sampled_support_sum {d J ℓ q : ℕ} (v : Fin d → ℤ)
    (seed : CopySeed J ℓ q) (j : ℕ) :
    ((integerSupport (sampledVector seed.1 j v)).card : ℝ) =
      ∑ i : Active v, activeIndicator v j i seed := by
  rw [← supportWeight_moment, moment_sampled _ (by simp)]
  apply Finset.sum_congr rfl
  intro i _
  simp [i.property]

lemma output_estimator_of_no_failure {d J ℓ q U K : ℕ} [Fact q.Prime]
    (w : ℤ → ℝ) (hw : w 0 = 0) (hdq : d < q) (hUq : 2 * U < q)
    (seed : CopySeed J ℓ q) (v : Fin d → ℤ)
    (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U)
    (hseed : seed ∉ recoveryFailure U K v) (j : Fin (J + 1))
    (hj : (integerSupport (sampledVector seed.1 j.val v)).card ≤ K) :
    output (d := d) w U K seed (finalSummary K seed v) =
      PairwiseBernoulli.estimator (fun i : Active v => w (v i.val))
        (activeIndicator v (selectedLevel (d := d) U K seed (finalSummary K seed v)).val)
        (dyadicProb (selectedLevel (d := d) U K seed (finalSummary K seed v)).val) seed := by
  rw [output_of_no_failure w hdq hUq seed v hv hseed j hj, moment_sampled w hw]
  simp only [PairwiseBernoulli.estimator, dyadicProb, one_div, div_inv_eq_mul]
  rw [mul_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring


lemma recoveryFailure_probability_le {d J ℓ q U K : ℕ} [Fact q.Prime]
    (hUq : 2 * U < q) (v : Fin d → ℤ)
    (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U) :
    (FiniteLaw.uniform (CopySeed J ℓ q)).prob (recoveryFailure U K v) ≤
      (J + 1 : ℕ) * ((d : ℝ) / q) := by
  simpa only [recoveryFailure, decodedAt, finalSummary, Fintype.card_fin] using
    ChecksumFailure.dense_decoder_union_bound (I := Fin (J + 1)) hUq
      (fun h j => sampledVector h j.val v)
      (fun h j => sampledVector_bounded h j.val v hv)

lemma single_copy_sixteenth_64 {ε K : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hK : 65536 / ε ^ 2 ≤ K) :
    (1 : ℝ) / 64 + 2 / K + 72 / (ε ^ 2 * K) < 1 / 16 := by
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hε21 : ε ^ 2 ≤ 1 := by nlinarith
  have hK0 : 0 < K := lt_of_lt_of_le (by positivity) hK
  have hprod : 65536 ≤ ε ^ 2 * K := by
    simpa only [mul_comm] using (div_le_iff₀ hε2).1 hK
  have hKbig : 65536 ≤ K := by nlinarith
  have h1 : 2 / K ≤ (2 : ℝ) / 65536 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hKbig
  have h2 : 72 / (ε ^ 2 * K) ≤ (72 : ℝ) / 65536 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hprod
  linarith

/-- Single-copy success for every bounded nonnegative weight. Its hypotheses
are parameters and the original pointwise assumptions on the weight; all hash,
recovery, adaptive selection and probability claims are proved above. -/
theorem bounded_weights_copy_failure {d J ℓ q U K : ℕ} [Fact q.Prime]
    (w : ℤ → ℝ) (hw : w 0 = 0)
    (hw1 : ∀ k, k ≠ 0 → 1 ≤ w k) (hw3 : ∀ k, w k ≤ 3)
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J)
    (hdq : d < q) (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (v : Fin d → ℤ) (hv : ∀ i, -(U : ℤ) ≤ v i ∧ v i ≤ U) :
    (FiniteLaw.uniform (CopySeed J ℓ q)).prob
      {seed | ε * moment w v < |output (d := d) w U K seed (finalSummary K seed v) - moment w v|}
      < 1 / 16 := by
  by_cases hs : (integerSupport v).card ≤ K
  · have he : {seed : CopySeed J ℓ q | ε * moment w v <
        |output (d := d) w U K seed (finalSummary K seed v) - moment w v|} = ∅ := by
      ext seed
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      rw [output_sparse_exact w hdq hUq seed v hv hs]
      have hF : 0 ≤ moment w v := by
        apply Finset.sum_nonneg
        intro i _
        by_cases hi : v i = 0
        · simp [hi, hw]
        · exact le_trans (by norm_num) (hw1 _ hi)
      simp only [sub_self, abs_zero, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_lt]
      exact mul_nonneg hε.le hF
    rw [he, FiniteLaw.uniform_prob]
    norm_num
  · have hsK : (K : ℝ) < (integerSupport v).card := by exact_mod_cast Nat.lt_of_not_ge hs
    have hcap : ((integerSupport v).card : ℝ) ≤ (2 : ℝ) ^ J := by
      have hc : (integerSupport v).card ≤ d :=
        (Finset.card_le_card (Finset.subset_univ _)).trans_eq (Fintype.card_fin d)
      exact_mod_cast hc.trans hdJ
    obtain ⟨L, hLpos, hLJ, hLlo, hLhi⟩ :=
      exists_useful_dyadic_level (by exact_mod_cast hK) hsK hcap
    let μ := FiniteLaw.uniform (CopySeed J ℓ q)
    let a : Active v → ℝ := fun i => w (v i.val)
    let B : ℕ → Active v → CopySeed J ℓ q → ℝ := activeIndicator v
    let select : CopySeed J ℓ q → ℕ := fun seed =>
      (selectedLevel (d := d) U K seed (finalSummary K seed v)).val
    let out : CopySeed J ℓ q → ℝ := fun seed => output (d := d) w U K seed (finalSummary K seed v)
    have hB : ∀ j ≤ L, PairwiseBernoulli μ (B j) (dyadicProb j) := by
      intro j hj
      exact activeIndicator_pairwise v hdℓ (hj.trans hLJ)
    have ha1 : ∀ i : Active v, 1 ≤ a i := fun i => hw1 _ i.property
    have ha3 : ∀ i : Active v, a i ≤ 3 := fun i => hw3 _
    have hsa : 0 < Fintype.card (Active v) := by rw [card_active]; omega
    have hKr : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hdrec : μ.prob (recoveryFailure U K v) ≤ (1 : ℝ) / 64 :=
      (recoveryFailure_probability_le hUq v hv).trans hqbig
    have hselect : ∀ seed, seed ∉ recoveryFailure U K v →
        (∑ i, B L i seed) ≤ (K : ℝ) → select seed ≤ L := by
      intro seed _ hsup
      have hsl : (integerSupport (sampledVector seed.1 L v)).card ≤ K := by
        have ht := sampled_support_sum v seed L
        dsimp [B] at hsup
        rw [← ht] at hsup
        exact_mod_cast hsup
      exact selectedLevel_sparse_le hdq hUq seed v hv ⟨L, by omega⟩ hsl
    have hout : ∀ seed, seed ∉ recoveryFailure U K v →
        (∑ i, B L i seed) ≤ (K : ℝ) →
        out seed = PairwiseBernoulli.estimator a (B (select seed))
          (dyadicProb (select seed)) seed := by
      intro seed hseed hsup
      have hsl : (integerSupport (sampledVector seed.1 L v)).card ≤ K := by
        have ht := sampled_support_sum v seed L
        dsimp [B] at hsup
        rw [← ht] at hsup
        exact_mod_cast hsup
      exact output_estimator_of_no_failure w hw hdq hUq seed v hv hseed ⟨L, by omega⟩ hsl
    have he := adaptive_failure_lt μ a B L hB ha1 ha3 hsa hε hKr
      (by simpa only [card_active] using hLlo) (by simpa only [card_active] using hLhi)
      (recoveryFailure U K v) hdrec select out hselect hout
    have hf : moment w v = ∑ i : Active v, a i := moment_active w hw v
    have hconst := single_copy_sixteenth_64 hε hε1 hKbig
    rw [hf]
    exact he.trans hconst

/-- The estimator guarantee applies to the final vector of every fixed stream,
without an intermediate-frequency or stream-length hypothesis. -/
theorem bounded_weights_one_pass {d J ℓ q U K : ℕ} [Fact q.Prime]
    (w : ℤ → ℝ) (hw : w 0 = 0)
    (hw1 : ∀ k, k ≠ 0 → 1 ≤ w k) (hw3 : ∀ k, w k ≤ 3)
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J)
    (hdq : d < q) (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (stream : List (Update d))
    (hv : ∀ i, -(U : ℤ) ≤ finalVector stream i ∧ finalVector stream i ≤ U) :
    (FiniteLaw.uniform (CopySeed J ℓ q)).prob
      {seed | ε * moment w (finalVector stream) <
        |output (d := d) w U K seed (run K seed stream) - moment w (finalVector stream)|} < 1 / 16 := by
  have he := bounded_weights_copy_failure w hw hw1 hw3 hdℓ hdJ hdq hUq hK hε hε1
    hKbig hqbig (finalVector stream) hv
  simpa only [run_finalVector] using he


/-- Median amplification of the actual independent finite seeds. -/
theorem bounded_weights_amplified {d J ℓ q U K : ℕ} [Fact q.Prime]
    (w : ℤ → ℝ) (hw : w 0 = 0)
    (hw1 : ∀ k, k ≠ 0 → 1 ≤ w k) (hw3 : ∀ k, w k ≤ 3)
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J)
    (hdq : d < q) (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (b : ℕ) (hR : 8 * Real.log (1 / δ) ≤ (2 * b + 1 : ℕ))
    (stream : List (Update d))
    (hv : ∀ i, -(U : ℤ) ≤ finalVector stream i ∧ finalVector stream i ≤ U) :
    ((FiniteLaw.uniform (CopySeed J ℓ q)).iid (Fin (2 * b + 1))).prob
      {seeds | ε * moment w (finalVector stream) <
        |median b (fun i => output (d := d) w U K (seeds i) (run K (seeds i) stream)) -
          moment w (finalVector stream)|} ≤ δ := by
  exact iid_median_failure_le_delta _ b _ _ _
    (bounded_weights_one_pass w hw hw1 hw3 hdℓ hdJ hdq hUq hK hε hε1 hKbig hqbig stream hv).le
    hδ hR

/-- The paper's witness has all weight assumptions of the finite-seed theorem. -/
theorem witness_stream_estimate {d J ℓ q U K : ℕ} [Fact q.Prime]
    (hdℓ : d ≤ 2 ^ ℓ) (hdJ : d ≤ 2 ^ J) (hdq : d < q)
    (hUq : 2 * U < q) (hK : 2 ≤ K)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ)
    (hKbig : 65536 / ε ^ 2 ≤ (K : ℝ))
    (hqbig : (J + 1 : ℕ) * ((d : ℝ) / q) ≤ 1 / 64)
    (b : ℕ) (hR : 8 * Real.log (1 / δ) ≤ (2 * b + 1 : ℕ))
    (stream : List (Update d))
    (hv : ∀ i, -(U : ℤ) ≤ finalVector stream i ∧ finalVector stream i ≤ U) :
    ((FiniteLaw.uniform (CopySeed J ℓ q)).iid (Fin (2 * b + 1))).prob
      {seeds | ε * moment f (finalVector stream) <
        |median b (fun i => output (d := d) f U K (seeds i) (run K (seeds i) stream)) -
          moment f (finalVector stream)|} ≤ δ :=
  bounded_weights_amplified f f_zero (fun _ h => f_ge_one_of_ne_zero h) f_le_three
    hdℓ hdJ hdq hUq hK hε hε1 hδ hKbig hqbig b hR stream hv

end Paper02.Streaming
