import Paper37.RenewalCompression
import Mathlib.Algebra.BigOperators.Fin

/-!
# The actual renewal memory bound

Only all-zero suffixes can preserve information about the older history. Their
entropy costs telescope to the entropy of the first-renewal position, capped at
the end of the finite block. All laws and kernels here are constructed from the
stationary renewal likelihood; no regeneration or information bound is assumed.
-/

namespace Paper37.RenewalCountdown

open Finset Compression Compression.Distribution Renewal RenewalCompression

lemma ageFrom_append (a : ℕ) (o s : List Bool) :
    ageFrom a (o ++ s) = ageFrom (ageFrom a o) s := by
  induction o generalizing a with
  | nil => rfl
  | cons b o ih => cases b <;> exact ih _

lemma ageFrom_forget (s : List Bool) (h : true ∈ s) (a b : ℕ) :
    ageFrom a s = ageFrom b s := by
  induction s generalizing a b with
  | nil => simp at h
  | cons c s ih =>
    cases c with
    | false => exact ih (by simpa using h) _ _
    | true => rfl

/-- The genuine stationary conditional forgets any older history once a renewal
is visible in the suffix. This is the renewal branch of Lemma D.1. -/
theorem next_after_visible_suffix (μ : Law) (o s : List Bool) (h : true ∈ s)
    (hs : 0 < blockMass μ s) (ho : 0 < blockMass μ (o ++ s)) :
    next μ (o ++ s) = next μ s := by
  have hc : conditional μ (o ++ s) = conditional μ s := by
    rw [conditional_visible_renewal μ (o ++ s) (List.mem_append.mpr (Or.inr h)) ho,
      conditional_visible_renewal μ s h hs, ageFrom_append, ageFrom_forget s h _ 0]
  apply Distribution.ext
  intro b
  cases b <;> simp only [next_false, next_true, hc]

/-- A positive suffix containing a renewal has exactly zero older-history information. -/
theorem visible_suffix_information_zero (μ : Law) (k : ℕ) (s : List Bool)
    (h : true ∈ s) (hs : 0 < blockMass μ s) :
    mutualInformation (olderPosterior μ k s) (fun o => next μ (o.val ++ s)) = 0 := by
  unfold mutualInformation conditionalKL
  rw [mixture_next_eq μ k s hs]
  apply sum_eq_zero
  intro o _
  by_cases hw : olderPosterior μ k s o = 0
  · simp [hw]
  · have hw' : 0 < olderPosterior μ k s o :=
      lt_of_le_of_ne ((olderPosterior μ k s).nonneg o) (Ne.symm hw)
    have ho : 0 < blockMass μ (o.val ++ s) := by
      rw [← olderPosterior_bayes μ k s o]
      exact mul_pos hs hw'
    dsimp only
    rw [next_after_visible_suffix μ o.val s h hs ho, Distribution.kl_self, mul_zero]

lemma no_true_eq_zeros (s : List Bool) (h : true ∉ s) :
    s = List.replicate s.length false := by
  induction s with
  | nil => rfl
  | cons b s ih =>
    cases b with
    | false =>
      have hs : true ∉ s := by simpa using h
      simpa only [List.length_cons, List.replicate_succ] using congrArg (false :: ·) (ih hs)
    | true => simp at h

/-- The one exceptional history of a given length. -/
def zeros (t : ℕ) : Word t := ⟨List.replicate t false, by simp⟩

/-- The entropy cost attached to an all-zero suffix. -/
noncomputable def zeroEntropy (μ : Law) (t : ℕ) : ℝ :=
  blockMass μ (List.replicate t false) * entropy (next μ (List.replicate t false))

lemma zeroEntropy_nonneg (μ : Law) (t : ℕ) : 0 ≤ zeroEntropy μ t :=
  mul_nonneg (blockMass_nonneg μ _) (entropy_nonneg _)

/-- All older-history information is bounded by the all-zero suffix contribution. -/
theorem memory_le_zeroEntropy (μ : Law) (k t : ℕ) :
    memory μ k t ≤ zeroEntropy μ t := by
  unfold memory
  calc
    _ ≤ ∑ s : Word t, if s = zeros t then
        blockMass μ s.val * entropy (next μ s.val) else 0 := by
      apply sum_le_sum
      intro s _
      by_cases hs : 0 < blockMass μ s.val
      · by_cases hz : s = zeros t
        · rw [if_pos hz]
          apply mul_le_mul_of_nonneg_left _ (blockMass_nonneg μ s.val)
          have hi := mutualInformation_le_output_entropy (olderPosterior μ k s.val)
            (fun o => next μ (o.val ++ s.val))
          rw [mixture_next_eq μ k s.val hs] at hi
          exact hi
        · rw [if_neg hz]
          have hseen : true ∈ s.val := by
            by_contra h
            apply hz
            apply Subtype.ext
            simpa only [zeros, s.property] using no_true_eq_zeros s.val h
          rw [visible_suffix_information_zero μ k s.val hseen hs, mul_zero]
      · have h0 : blockMass μ s.val = 0 :=
          le_antisymm (le_of_not_gt hs) (blockMass_nonneg μ s.val)
        simp [h0]
    _ = zeroEntropy μ t := by simp [zeroEntropy, zeros]

/-- Exact entropy splitting at the next observation, including null histories. -/
theorem weighted_next_entropy (μ : Law) (x : List Bool) :
    blockMass μ x * entropy (next μ x) =
      Real.negMulLog (blockMass μ (x ++ [false])) +
        Real.negMulLog (blockMass μ (x ++ [true])) - Real.negMulLog (blockMass μ x) := by
  have h : (∑ b : Bool, Real.negMulLog (blockMass μ x * next μ x b)) =
      Real.negMulLog (blockMass μ x) + blockMass μ x * entropy (next μ x) := by
    simp_rw [Real.negMulLog_mul, sum_add_distrib, ← sum_mul, (next μ x).total, one_mul,
      ← mul_sum, ← entropy_eq_sum_negMulLog]
  simp_rw [weighted_next] at h
  simp only [Fintype.sum_bool] at h
  linarith

/-- Splitting the all-zero event into first renewal now versus continued zeros. -/
theorem zeroEntropy_split (μ : Law) (t : ℕ) :
    zeroEntropy μ t = Real.negMulLog (residual μ (t + 1) / mean μ) +
      Real.negMulLog (tail μ t / mean μ) - Real.negMulLog (residual μ t / mean μ) := by
  unfold zeroEntropy
  rw [weighted_next_entropy]
  have hz : List.replicate t false ++ [false] = List.replicate (t + 1) false := by
    simpa using (List.replicate_add t 1 false).symm
  rw [hz, blockMass_zeros, blockMass_first_renewal]
  simp only [ordinary, tail_zero, mul_one, blockMass_zeros]

/-- The actual first-renewal location, with all positions beyond `N` merged into
one value. Index `j < N` means first renewal at `j+1`; index `N` means no renewal. -/
noncomputable def countdown (μ : Law) (N : ℕ) : Distribution (Fin (N + 1)) where
  mass j := if j.val < N then tail μ j.val / mean μ else residual μ N / mean μ
  nonneg j := by
    split_ifs
    · exact div_nonneg (tail_nonneg μ j.val) (mean_pos μ).le
    · exact div_nonneg (residual_nonneg μ N) (mean_pos μ).le
  total := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc, Fin.val_last, Fin.is_lt, ↓reduceIte, lt_self_iff_false]
    simp only [div_eq_mul_inv, ← sum_mul]
    rw [Fin.sum_univ_eq_sum_range, ← add_mul, ← residual_tail_identity]
    exact mul_inv_cancel₀ (mean_pos μ).ne'

/-- Entropy of the actual capped countdown. -/
theorem countdown_entropy (μ : Law) (N : ℕ) :
    entropy (countdown μ N) =
      (∑ j ∈ range N, Real.negMulLog (tail μ j / mean μ)) +
        Real.negMulLog (residual μ N / mean μ) := by
  rw [entropy_eq_sum_negMulLog, Fin.sum_univ_castSucc]
  simp only [countdown, Fin.coe_castSucc, Fin.val_last, Fin.is_lt, ↓reduceIte, lt_self_iff_false]
  rw [← Fin.sum_univ_eq_sum_range]

/-- The all-zero entropy costs telescope to one finite countdown entropy. -/
theorem sum_zeroEntropy_eq_countdown_entropy (μ : Law) (N : ℕ) :
    (∑ t ∈ range N, zeroEntropy μ t) = entropy (countdown μ N) := by
  rw [countdown_entropy]
  induction N with
  | zero => simp [residual_zero, div_self (mean_pos μ).ne']
  | succ N ih =>
    rw [sum_range_succ, sum_range_succ, ih, zeroEntropy_split]
    ring

/-- The complete renewal memory bound in Lemma D.2, directly for the stationary
source law. The older-history lengths can be arbitrary at each suffix length. -/
theorem renewal_memory_sum_bound (μ : Law) (n : ℕ) (olderLength : ℕ → ℕ) :
    (∑ t ∈ range n, memory μ (olderLength (t + 1)) (t + 1)) ≤ Real.log (n + 2) := by
  have ht : (∑ t ∈ range n, memory μ (olderLength (t + 1)) (t + 1)) ≤
      ∑ t ∈ range n, zeroEntropy μ (t + 1) :=
    sum_le_sum (fun t _ => memory_le_zeroEntropy μ _ _)
  have hs : (∑ t ∈ range n, zeroEntropy μ (t + 1)) ≤
      ∑ t ∈ range (n + 1), zeroEntropy μ t := by
    rw [sum_range_succ']
    exact le_add_of_nonneg_right (zeroEntropy_nonneg μ 0)
  have he := entropy_le_log_card (countdown μ (n + 1))
  simp only [Fintype.card_fin, Nat.cast_add, Nat.cast_one] at he
  have hlog : Real.log ((n : ℝ) + 1 + 1) = Real.log ((n : ℝ) + 2) := by congr 1; ring
  rw [hlog] at he
  exact ht.trans (hs.trans ((sum_zeroEntropy_eq_countdown_entropy μ (n + 1)) ▸ he))

end Paper37.RenewalCountdown
