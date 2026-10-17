import Paper37.RenewalCountdown

/-!
# Finite joint form of suffix regeneration (D.1)

The inclusive countdown is used by a length-`t` suffix and one next bit only
through its cap at `t+2`. The value below is that capped countdown minus one.
It is determined by the first renewal in the observed `t+1` symbols, with the
single terminal value `t+1` denoting no renewal. The theorem is the ordinary
multiplicative finite-mass definition of conditional independence, and includes
null conditioning events without division.
-/
namespace Paper37.SuffixRegeneration

open Finset Compression Compression.Distribution Renewal RenewalCompression RenewalCountdown

/-- First one, indexed from zero; the sentinel for no one is the list's length. -/
def firstOneIndex : List Bool → ℕ
  | [] => 0
  | false :: x => firstOneIndex x + 1
  | true :: _ => 0

lemma firstOneIndex_le_length (x : List Bool) : firstOneIndex x ≤ x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [firstOneIndex]; omega

lemma firstOneIndex_zeros_append (n : ℕ) (x : List Bool) :
    firstOneIndex (List.replicate n false ++ x) = n + firstOneIndex x := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.replicate_succ, List.cons_append, firstOneIndex, ih]; omega

lemma firstOneIndex_visible (s : List Bool) (hs : true ∈ s) (x y : List Bool) :
    firstOneIndex (s ++ x) = firstOneIndex (s ++ y) := by
  induction s with
  | nil => simp at hs
  | cons b s ih =>
    cases b with
    | false =>
      change firstOneIndex (s ++ x) + 1 = firstOneIndex (s ++ y) + 1
      exact congrArg (· + 1) (ih (by simpa using hs))
    | true => rfl

/-- Capped inclusive countdown minus one at the start of a suffix. -/
def countdownValue {t : ℕ} (s : Word t) (y : Bool) : Fin (t + 2) :=
  ⟨firstOneIndex (s.val ++ [y]), by
    have h := firstOneIndex_le_length (s.val ++ [y])
    rw [List.length_append, s.property] at h
    simp only [List.length_singleton] at h
    omega⟩

lemma countdownValue_visible {t : ℕ} (s : Word t) (hs : true ∈ s.val) (y y' : Bool) :
    countdownValue s y = countdownValue s y' :=
  Fin.ext (firstOneIndex_visible s.val hs [y] [y'])

@[simp] lemma countdownValue_zeros_true (t : ℕ) :
    (countdownValue (zeros t) true).val = t := by
  simp [countdownValue, zeros, firstOneIndex_zeros_append, firstOneIndex]

@[simp] lemma countdownValue_zeros_false (t : ℕ) :
    (countdownValue (zeros t) false).val = t + 1 := by
  simp [countdownValue, zeros, firstOneIndex_zeros_append, firstOneIndex]

/-- The visible-renewal likelihood factorization holds even at null histories. -/
theorem visible_suffix_extension_factor (μ : Law) (o s : List Bool)
    (hs : true ∈ s) (y : Bool) :
    blockMass μ ((o ++ s) ++ [y]) = blockMass μ (o ++ s) * next μ s y := by
  rw [← weighted_next μ (o ++ s) y]
  by_cases ho : 0 < blockMass μ (o ++ s)
  · have hsp : 0 < blockMass μ s :=
      lt_of_lt_of_le ho (older_component_le μ o.length s ⟨o, rfl⟩)
    rw [next_after_visible_suffix μ o s hs hsp ho]
  · have hz : blockMass μ (o ++ s) = 0 :=
      le_antisymm (le_of_not_gt ho) (blockMass_nonneg μ _)
    simp [hz]

/-- The actual joint mass of older history, suffix, next bit, and capped countdown. -/
noncomputable def jointMass (μ : Law) {k t : ℕ} (o : Word k) (s : Word t)
    (y : Bool) (c : Fin (t + 2)) : ℝ :=
  if countdownValue s y = c then blockMass μ ((o.val ++ s.val) ++ [y]) else 0

/-- Each fixed suffix/countdown slice has rank one in older-history and next-bit
coordinates. This is a division-free conditional-independence certificate. -/
theorem jointMass_rank_one (μ : Law) {k t : ℕ} (o o' : Word k) (s : Word t)
    (y y' : Bool) (c : Fin (t + 2)) :
    jointMass μ o s y c * jointMass μ o' s y' c =
      jointMass μ o s y' c * jointMass μ o' s y c := by
  by_cases hs : true ∈ s.val
  · have hc : ∀ b, countdownValue s b = countdownValue s false :=
      fun b => countdownValue_visible s hs b false
    simp only [jointMass, hc]
    by_cases h : countdownValue s false = c
    · simp only [h, ↓reduceIte, visible_suffix_extension_factor μ _ _ hs]
      ring
    · simp [h]
  · have hz : s = zeros t := by
      apply Subtype.ext
      simpa only [zeros, s.property] using no_true_eq_zeros s.val hs
    subst s
    cases y <;> cases y'
    · ring
    · simp only [jointMass, Fin.ext_iff, countdownValue_zeros_true, countdownValue_zeros_false]
      split_ifs <;> first | omega | simp_all
    · simp only [jointMass, Fin.ext_iff, countdownValue_zeros_true, countdownValue_zeros_false]
      split_ifs <;> first | omega | simp_all
    · ring

/-- Lemma D.1 in its exact finite joint-law formulation:
`Y` and the older history are conditionally independent given suffix and capped
countdown. No positivity premise is required because all expressions are masses. -/
theorem suffix_regeneration (μ : Law) {k t : ℕ} (o : Word k) (s : Word t)
    (y : Bool) (c : Fin (t + 2)) :
    jointMass μ o s y c * (∑ o' : Word k, ∑ y' : Bool, jointMass μ o' s y' c) =
      (∑ y' : Bool, jointMass μ o s y' c) * (∑ o' : Word k, jointMass μ o' s y c) := by
  simp_rw [mul_sum, sum_mul]
  apply sum_congr rfl
  intro o' _
  apply sum_congr rfl
  intro y' _
  exact jointMass_rank_one μ o o' s y y' c

/-- The joint masses above form an actual normalized probability distribution. -/
noncomputable def jointDistribution (μ : Law) (k t : ℕ) :
    Distribution (Word k × Word t × Bool × Fin (t + 2)) where
  mass x := jointMass μ x.1 x.2.1 x.2.2.1 x.2.2.2
  nonneg x := by unfold jointMass; split_ifs <;> first | exact blockMass_nonneg μ _ | exact le_rfl
  total := by
    simp only [Fintype.sum_prod_type, jointMass]
    simp only [sum_ite_eq, mem_univ, ↓reduceIte]
    rw [sum_comm]
    have hs : ∀ s : Word t, (∑ o : Word k, ∑ y : Bool,
        blockMass μ ((o.val ++ s.val) ++ [y])) = blockMass μ s.val := by
      intro s
      calc
        _ = ∑ o : Word k, blockMass μ (o.val ++ s.val) := by
          apply sum_congr rfl
          intro o _
          rw [Fintype.sum_bool]
          simpa only [add_comm] using (blockMass_right_consistency μ (o.val ++ s.val)).symm
        _ = _ := stationary_suffix_marginal μ k s.val
    simp_rw [hs]
    exact (blockDistribution μ t).total

end Paper37.SuffixRegeneration
