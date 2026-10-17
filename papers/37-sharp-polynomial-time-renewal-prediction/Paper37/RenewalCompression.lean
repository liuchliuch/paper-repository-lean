import Paper37.Compression
import Paper37.RenewalLikelihood
import Paper37.Boundary
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.Vector.Snoc
import Mathlib.Data.List.Induction

/-!
# The actual stationary renewal laws in the finite information framework

This module constructs normalized finite distributions from `Renewal.blockMass`.
Stationarity and Bayes disintegration below are proved from those block masses,
not postulated as properties of a prediction risk.
-/

namespace Paper37.RenewalCompression

open Finset Compression Compression.Distribution Renewal

abbrev Word (n : ℕ) := List.Vector Bool n

/-- The length-indexed finite alphabet has exactly the source's enumerated words. -/
lemma sum_word (n : ℕ) (f : List Bool → ℝ) :
    (∑ x : Word n, f x.val) = wordSum n f := by
  classical
  unfold wordSum
  rw [← List.sum_toFinset _ (words_nodup n)]
  refine sum_bij (fun x _ => x.val) ?_ ?_ ?_ ?_
  · intro x _
    exact List.mem_toFinset.mpr ((mem_words n x.val).mpr x.property)
  · intro x _ y _ h
    exact Subtype.ext h
  · intro x hx
    exact ⟨⟨x, (mem_words n x).mp (List.mem_toFinset.mp hx)⟩, mem_univ _, rfl⟩
  · intro x _
    rfl

lemma wordSum_add (n : ℕ) (f g : List Bool → ℝ) :
    wordSum n (fun x => f x + g x) = wordSum n f + wordSum n g := by
  induction n generalizing f g with
  | zero => simp
  | succ n ih => simp only [wordSum_step, ih]; ring

/-- Exact stationarity for any number of unobserved earlier symbols. -/
theorem stationary_left_marginal (μ : Law) (k : ℕ) (s : List Bool) :
    wordSum k (fun o => blockMass μ (o ++ s)) = blockMass μ s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [wordSum_step, ← wordSum_add]
    simp only [List.cons_append]
    simp_rw [← blockMass_left_consistency]
    exact ih

/-- The same stationarity identity as a finite probability sum. -/
theorem stationary_suffix_marginal (μ : Law) (k : ℕ) (s : List Bool) :
    (∑ o : Word k, blockMass μ (o.val ++ s)) = blockMass μ s := by
  exact (sum_word k (fun o => blockMass μ (o ++ s))).trans (stationary_left_marginal μ k s)

/-- Actual stationary length-`n` block law on the binary alphabet. -/
noncomputable def blockDistribution (μ : Law) (n : ℕ) : Distribution (Word n) where
  mass x := blockMass μ x.val
  nonneg x := blockMass_nonneg μ x.val
  total := by rw [sum_word]; exact blockMass_normalized μ n

@[simp] lemma blockDistribution_apply (μ : Law) (n : ℕ) (x : Word n) :
    blockDistribution μ n x = blockMass μ x.val := rfl

/-- An actual Bernoulli probability distribution on `Bool`. -/
noncomputable def binary (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Distribution Bool where
  mass b := if b then p else 1 - p
  nonneg b := by cases b <;> simp_all
  total := by simp

@[simp] lemma binary_true (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binary p hp0 hp1 true = p := rfl

@[simp] lemma binary_false (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binary p hp0 hp1 false = 1 - p := rfl

/-- Exact conversion between the finite-alphabet KL and the source binary formula. -/
theorem binary_klReal {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    Distribution.kl (binary p hp0 hp1) (binary q hq0.le hq1.le) = Boundary.klReal p q := by
  rw [Boundary.klReal_eq_crossEntropy hq0.ne' (ne_of_lt hq1)]
  simp [Distribution.kl, Real.binEntropy, Real.log_inv]
  ring

/-- Endpoint-safe conversion to the extended Bernoulli KL used by the risk. -/
theorem binary_kl_extended {p q : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hq0 : 0 < q) (hq1 : q < 1) :
    Boundary.kl p q = ENNReal.ofReal
      (Distribution.kl (binary p hp0 hp1) (binary q hq0.le hq1.le)) := by
  rw [binary_klReal hp0 hp1 hq0 hq1]
  simp [Boundary.kl, hq0.ne', ne_of_lt hq1]

/-- The genuine stationary next-symbol law, including the all-zero history. -/
noncomputable def next (μ : Law) (x : List Bool) : Distribution Bool :=
  binary (conditional μ x) (conditional_mem_unitInterval μ x).1
    (conditional_mem_unitInterval μ x).2

@[simp] lemma next_true (μ : Law) (x : List Bool) : next μ x true = conditional μ x := rfl
@[simp] lemma next_false (μ : Law) (x : List Bool) : next μ x false = 1 - conditional μ x := rfl

/-- True conditional probabilities recover the extension masses, including null histories. -/
theorem weighted_next (μ : Law) (x : List Bool) (b : Bool) :
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

/-- Each older-history mass is bounded by the actual suffix mass. -/
lemma older_component_le (μ : Law) (k : ℕ) (s : List Bool) (o : Word k) :
    blockMass μ (o.val ++ s) ≤ blockMass μ s := by
  rw [← stationary_suffix_marginal μ k s]
  exact single_le_sum (fun j _ => blockMass_nonneg μ (j.val ++ s)) (mem_univ o)

/-- Conditional law of the earlier `k` symbols given a suffix, computed from
actual renewal probabilities; the null-event version is the stationary `k`-block law. -/
noncomputable def olderPosterior (μ : Law) (k : ℕ) (s : List Bool) : Distribution (Word k) := by
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

/-- Bayes' rule for the actual suffix disintegration, including null suffixes. -/
theorem olderPosterior_bayes (μ : Law) (k : ℕ) (s : List Bool) (o : Word k) :
    blockMass μ s * olderPosterior μ k s o = blockMass μ (o.val ++ s) := by
  classical
  by_cases h : 0 < blockMass μ s
  · simp only [olderPosterior, h, ↓reduceIte]
    exact mul_div_cancel₀ _ h.ne'
  · have hs : blockMass μ s = 0 := le_antisymm (le_of_not_gt h) (blockMass_nonneg μ s)
    have ho : blockMass μ (o.val ++ s) = 0 :=
      le_antisymm (hs ▸ older_component_le μ k s o) (blockMass_nonneg μ _)
    rw [hs, zero_mul, ho]

/-- Stationarity transports the joint suffix/next-bit marginal, not just the suffix. -/
theorem stationary_suffix_next (μ : Law) (k : ℕ) (s : List Bool) (b : Bool) :
    (∑ o : Word k, blockMass μ (o.val ++ s) * next μ (o.val ++ s) b) =
      blockMass μ s * next μ s b := by
  simp_rw [weighted_next]
  simp only [List.append_assoc]
  exact stationary_suffix_marginal μ k (s ++ [b])

/-- The actual coarsened stationary conditional is the Bayesian mixture of the
full conditionals on every positive-probability suffix. -/
theorem mixture_next_eq (μ : Law) (k : ℕ) (s : List Bool) (hs : 0 < blockMass μ s) :
    mixture (olderPosterior μ k s) (fun o => next μ (o.val ++ s)) = next μ s := by
  apply Distribution.ext
  intro b
  apply (mul_left_cancel₀ hs.ne')
  simp only [mixture_apply, mul_sum]
  simp_rw [← mul_assoc, olderPosterior_bayes]
  exact stationary_suffix_next μ k s b

/-- Conditional information in the older history, averaged under the actual suffix law. -/
noncomputable def memory (μ : Law) (k t : ℕ) : ℝ :=
  ∑ s : Word t, blockMass μ s.val * mutualInformation (olderPosterior μ k s.val)
    (fun o => next μ (o.val ++ s.val))

/-- Full-history log loss for a prediction that uses only the last `t` symbols. -/
noncomputable def suffixRisk (μ : Law) (k t : ℕ) (q : Word t → Distribution Bool) : ℝ :=
  ∑ s : Word t, ∑ o : Word k, blockMass μ (o.val ++ s.val) *
    Distribution.kl (next μ (o.val ++ s.val)) (q s)

/-- Exact original stationary renewal version of (D.3), with all probability
kernels derived from `blockMass` and the actual suffix marginal. -/
theorem suffixRisk_decomposition (μ : Law) (k t : ℕ) (q : Word t → Distribution Bool) :
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

end Paper37.RenewalCompression
