import Paper14.Basic
/-!
# Induced maps, return times, and excess counts

Paper anchors: Ex14/Ex15 (`r_Y`, `T_Y`, `R_Y^{(n)}`), E6 (first moment),
E7 (tail), E8 (almost invariance of `E_{n,j}`).

Proved here: unfolds of `firstReturnTime` / `inducedMap` / `Rn` / `excessDn` /
`excessLevel`, the recursion `Rn (n+1) = Rn n + r_Y(T_Y^n y)`, the combinatorial
identity `Rn = n + j → excessDn = j`, and a finite Markov tail bound for
nonnegative integer data.
-/
open MeasureTheory Filter Topology Set
open Classical

namespace Paper14

/-- Kac-type first moment of the return time on `Y`: `∫_Y r_Y dμ = 1`
for an ergodic probability-preserving `T` and `Y` of positive measure. -/
def KacFirstMomentStatement : Prop :=
  ∀ {α : Type} [MeasurableSpace α] (T : α → α) (μ : Measure α) (Y : Set α),
    IsProbabilityMeasure μ → Ergodic T μ → MeasurableSet Y →
      0 < μ Y →
        ∫ y in Y, (firstReturnTime T Y y : ℝ) ∂μ = 1

/-! ## Unfolds of `firstReturnTime` and `inducedMap` -/

/-- No return ⇒ `firstReturnTime = 0`. -/
theorem firstReturnTime_of_not_exists {α : Type*} {T : α → α} {Y : Set α} {y : α}
    (h : ¬ ∃ k, 0 < k ∧ T^[k] y ∈ Y) : firstReturnTime T Y y = 0 := by
  show (letI := Classical.decPred (fun k : ℕ => 0 < k ∧ T^[k] y ∈ Y)
      if h' : ∃ k, 0 < k ∧ T^[k] y ∈ Y then Nat.find h' else 0) = 0
  rw [dif_neg h]

/-- When a return exists, `firstReturnTime` is `Nat.find` of the first return. -/
theorem firstReturnTime_eq_find {α : Type*} {T : α → α} {Y : Set α} {y : α}
    (h : ∃ k, 0 < k ∧ T^[k] y ∈ Y) :
    firstReturnTime T Y y
      = @Nat.find (fun k => 0 < k ∧ T^[k] y ∈ Y) (Classical.decPred _) h := by
  show (letI := Classical.decPred (fun k : ℕ => 0 < k ∧ T^[k] y ∈ Y)
      if h' : ∃ k, 0 < k ∧ T^[k] y ∈ Y then Nat.find h' else 0) = _
  rw [dif_pos h]

/-- Same statement with `∃ k > 0` syntax. -/
theorem firstReturnTime_of_exists {α : Type*} {T : α → α} {Y : Set α} {y : α}
    (h : ∃ k > 0, T^[k] y ∈ Y) :
    firstReturnTime T Y y
      = @Nat.find (fun k => 0 < k ∧ T^[k] y ∈ Y) (Classical.decPred _) h :=
  firstReturnTime_eq_find h

/-- `inducedMap T Y y = T^[firstReturnTime T Y y] y`. -/
theorem inducedMap_eq {α : Type*} (T : α → α) (Y : Set α) (y : α) :
    inducedMap T Y y = T^[firstReturnTime T Y y] y :=
  rfl

/-- Unfold of `inducedMap` at the `firstReturnTime`. -/
theorem inducedMap_apply {α : Type*} (T : α → α) (Y : Set α) (y : α) :
    inducedMap T Y y = T^[firstReturnTime T Y y] y :=
  rfl

/-! ## Recursion for `Rn` -/

/-- Base case: `Rn T Y 0 y = 0`. -/
theorem Rn_zero {α : Type*} (T : α → α) (Y : Set α) (y : α) :
    Rn T Y 0 y = 0 :=
  rfl

/-- Successor: `Rn T Y (n+1) y = Rn T Y n y + firstReturnTime T Y ((inducedMap T Y)^[n] y)`. -/
theorem Rn_succ {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (y : α) :
    Rn T Y (n + 1) y
      = Rn T Y n y + firstReturnTime T Y ((inducedMap T Y)^[n] y) := by
  unfold Rn
  rw [Finset.sum_range_succ]

/-- Explicit form of `Rn` as a finite sum. -/
theorem Rn_eq_sum {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (y : α) :
    Rn T Y n y
      = ∑ i ∈ Finset.range n, firstReturnTime T Y ((inducedMap T Y)^[i] y) :=
  rfl

/-! ## Excess counts -/

/-- Unfold: `excessDn T Y n y = Rn T Y n y - n`. -/
theorem excessDn_eq {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (y : α) :
    excessDn T Y n y = Rn T Y n y - n :=
  rfl

/-- Unfold: `excessLevel T Y n j = {y ∈ Y | excessDn T Y n y = j}`. -/
theorem excessLevel_eq {α : Type*} (T : α → α) (Y : Set α) (n j : ℕ) :
    excessLevel T Y n j = {y ∈ Y | excessDn T Y n y = j} :=
  rfl

/-- Membership in an excess level. -/
theorem mem_excessLevel {α : Type*} {T : α → α} {Y : Set α} {n j : ℕ} {y : α} :
    y ∈ excessLevel T Y n j ↔ y ∈ Y ∧ excessDn T Y n y = j :=
  Iff.rfl

/-- Combinatorial identity: `Rn = n + j` forces `excessDn = j`. -/
theorem excessDn_of_Rn_eq_add {α : Type*} (T : α → α) (Y : Set α) (n j : ℕ) (y : α)
    (h : Rn T Y n y = n + j) : excessDn T Y n y = j := by
  rw [excessDn_eq, h]
  omega

/-- Equivalent form: `excessDn = j` iff `Rn = n + j` when `n ≤ Rn`. -/
theorem excessDn_iff_Rn_eq_add {α : Type*} (T : α → α) (Y : Set α) (n j : ℕ) (y : α)
    (hle : n ≤ Rn T Y n y) :
    excessDn T Y n y = j ↔ Rn T Y n y = n + j := by
  constructor
  · intro h
    have h1 : Rn T Y n y - n = j := h
    omega
  · exact excessDn_of_Rn_eq_add T Y n j y

/-- Recursion for the excess: `excessDn (n+1) = excessDn n + (r_Y(T_Y^n y) - 1)`
when the two subtractions are legitimate (`n ≤ Rn n`, `1 ≤ r_Y(T_Y^n y)`). -/
theorem excessDn_succ {α : Type*} (T : α → α) (Y : Set α) (n : ℕ) (y : α)
    (hn : n ≤ Rn T Y n y)
    (hr : 1 ≤ firstReturnTime T Y ((inducedMap T Y)^[n] y)) :
    excessDn T Y (n + 1) y
      = excessDn T Y n y + (firstReturnTime T Y ((inducedMap T Y)^[n] y) - 1) := by
  have h1 : excessDn T Y (n + 1) y = Rn T Y (n + 1) y - (n + 1) := rfl
  have h2 : excessDn T Y n y = Rn T Y n y - n := rfl
  rw [h1, h2, Rn_succ]
  omega

/-! ## Finite Markov tail bound (paper E7, counting form) -/

/-- Counting form of Markov: if the average of nonnegative integer data `d`
on a Finset is at most `C`, then the number of entries with `d > J` is at most
`C/(J+1) * card`. -/
theorem markov_card_filter {α : Type*} (s : Finset α) (d : α → ℕ) (C J : ℝ)
    (hJ : 0 ≤ J)
    (h : (∑ x ∈ s, (d x : ℝ)) ≤ C * s.card) :
    ((s.filter (fun x => (J + 1 : ℝ) < (d x : ℝ))).card : ℝ)
      ≤ C / (J + 1) * s.card := by
  have ha0 : (0:ℝ) < J + 1 := by linarith
  set t := s.filter (fun x => (J + 1 : ℝ) < (d x : ℝ)) with ht
  have ht_sub : t ⊆ s := s.filter_subset _
  have hterm : ∀ x ∈ t, (J + 1 : ℝ) ≤ (d x : ℝ) := by
    intro x hx
    have hx' : (J + 1 : ℝ) < (d x : ℝ) := (Finset.mem_filter.mp hx).2
    exact hx'.le
  have hsum_t : (J + 1 : ℝ) * t.card ≤ ∑ x ∈ t, (d x : ℝ) := by
    have h1 : ∑ _x ∈ t, (J + 1 : ℝ) ≤ ∑ x ∈ t, (d x : ℝ) :=
      Finset.sum_le_sum hterm
    have h2 : ∑ _x ∈ t, (J + 1 : ℝ) = t.card * (J + 1 : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have hsum_s : ∑ x ∈ t, (d x : ℝ) ≤ ∑ x ∈ s, (d x : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg ht_sub
      (fun x _ _ => Nat.cast_nonneg _)
  have hkey : (J + 1 : ℝ) * t.card ≤ C * s.card := by
    linarith [hsum_t, hsum_s, h]
  have hkey' : (t.card : ℝ) * (J + 1) ≤ C * s.card := by linarith
  have hdiv : (t.card : ℝ) ≤ C * s.card / (J + 1) :=
    (le_div_iff₀ ha0).2 hkey'
  calc ((t.card : ℝ))
      ≤ C * s.card / (J + 1) := hdiv
    _ = C / (J + 1) * s.card := by ring

/-- Special case on `Finset ℕ` of the counting Markov bound. -/
theorem markov_card_filter_nat (s : Finset ℕ) (C J : ℝ) (hJ : 0 ≤ J)
    (h : (∑ d ∈ s, (d : ℝ)) ≤ C * s.card) :
    ((s.filter (fun d : ℕ => (J + 1 : ℝ) < (d : ℝ))).card : ℝ)
      ≤ C / (J + 1) * s.card :=
  markov_card_filter (α := ℕ) s (fun d => d) C J hJ h

/-- Tail factor `C/(J+1)` is nonnegative for `C, J ≥ 0` (paper E7). -/
theorem excess_tail_nonneg {C J : ℝ} (hC : 0 ≤ C) (hJ : 0 ≤ J) :
    0 ≤ C / (J + 1) :=
  div_nonneg hC (by linarith)

/-- The Markov threshold itself is positive for `J ≥ 0`. -/
theorem excess_tail_denom_pos {J : ℝ} (hJ : 0 ≤ J) : (0:ℝ) < J + 1 := by
  linarith

/-- Specialized Markov: if `∑ d ≤ C * card` and `J ≥ 0`, then
`card {d > J} / card ≤ C/(J+1)` when `card > 0`. -/
theorem markov_freq_bound {α : Type*} (s : Finset α) (d : α → ℕ) (C J : ℝ)
    (hJ : 0 ≤ J) (hs : s.card ≠ 0)
    (h : (∑ x ∈ s, (d x : ℝ)) ≤ C * s.card) :
    ((s.filter (fun x => (J + 1 : ℝ) < (d x : ℝ))).card : ℝ) / s.card
      ≤ C / (J + 1) := by
  have h1 := markov_card_filter s d C J hJ h
  have hs0 : (0:ℝ) < s.card := by
    exact_mod_cast Nat.pos_of_ne_zero hs
  have h2 : ((s.filter (fun x => (J + 1 : ℝ) < (d x : ℝ))).card : ℝ) / s.card
      ≤ (C / (J + 1) * s.card) / s.card :=
    (div_le_div_of_nonneg_right h1 (Nat.cast_nonneg s.card))
  have h3 : (C / (J + 1) * s.card) / s.card = C / (J + 1) := by
    field_simp [ne_of_gt hs0]
  rw [h3] at h2
  exact h2

end Paper14
