import Paper02.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.Card

/-!
# An executable bounded-space evaluator for the witness

`parityScan` is a tail-state binary scan. Its only live registers are a fuel
counter, the remaining input and a single parity bit. The fuel is bounded by
`|k|+1`; it is not a recursion stack in the transition-system semantics below.
The register-cardinality bound includes the fuel counter.
-/

namespace Paper02.WeightEval

/-- One parity bit is enough for the adjacent-ones count. -/
def parityScan : ℕ → ℕ → ZMod 2 → ZMod 2
  | 0, _, p => p
  | _ + 1, 0, p => p
  | fuel + 1, k + 1, p =>
      parityScan fuel ((k + 1) / 2)
        (p + if (k + 1) % 4 = 3 then 1 else 0)

lemma parityScan_eq (fuel k : ℕ) (p : ZMod 2) :
    parityScan fuel k p = p + (adjacentOnesCountAux fuel k : ZMod 2) := by
  induction fuel generalizing k p with
  | zero => simp [parityScan, adjacentOnesCountAux]
  | succ fuel ih =>
    cases k with
    | zero => simp [parityScan, adjacentOnesCountAux]
    | succ k =>
      rw [parityScan, adjacentOnesCountAux, ih]
      split_ifs <;> push_cast <;> ring

/-- Computable natural-valued version of the paper's real-valued target. -/
def weight (k : ℤ) : ℕ :=
  if k = 0 then 0 else
    if parityScan (k.natAbs + 1) k.natAbs 0 = 0 then 3 else 1

lemma parityScan_zero_iff_even (k : ℕ) :
    parityScan (k + 1) k 0 = 0 ↔ Even (adjacentOnesCount k) := by
  rw [parityScan_eq]
  simp only [zero_add]
  rw [ZMod.natCast_eq_zero_iff, even_iff_two_dvd]
  rfl

lemma weight_cast (k : ℤ) : (weight k : ℝ) = f k := by
  by_cases hk : k = 0
  · simp [weight, hk, f_zero]
  rw [weight, if_neg hk, f_of_ne_zero hk]
  by_cases he : Even (adjacentOnesCount k.natAbs)
  · rw [if_pos ((parityScan_zero_iff_even _).mpr he), rudinShapiro_of_even he]
    norm_num
  · have ho : Odd (adjacentOnesCount k.natAbs) := Nat.not_even_iff_odd.mp he
    rw [if_neg (fun h => he ((parityScan_zero_iff_even _).mp h)), rudinShapiro_of_odd ho]
    norm_num

lemma weight_zero : weight 0 = 0 := by simp [weight]
lemma weight_pos {k : ℤ} (hk : k ≠ 0) : 1 ≤ weight k := by
  unfold weight
  simp only [if_neg hk]
  split_ifs <;> omega
lemma weight_le_three (k : ℤ) : weight k ≤ 3 := by
  unfold weight
  split_ifs <;> omega
lemma weight_mem (k : ℤ) : weight k ∈ ({0, 1, 3} : Finset ℕ) := by
  unfold weight
  split_ifs <;> simp
lemma weight_even (k : ℤ) : weight (-k) = weight k := by
  unfold weight
  simp

/-- The entire live state of the tail-state evaluator. -/
structure ScanState (U : ℕ) where
  fuel : Fin (U + 2)
  remaining : Fin (U + 1)
  parity : ZMod 2
  deriving Fintype, DecidableEq

/-- One transition; at zero fuel or remaining input the machine is stationary. -/
def scanStep {U : ℕ} (s : ScanState U) : ScanState U :=
  if h : s.fuel.val = 0 ∨ s.remaining.val = 0 then s else
    { fuel := ⟨s.fuel.val - 1, by omega⟩
      remaining := ⟨s.remaining.val / 2,
        lt_of_le_of_lt (Nat.div_le_self _ _) s.remaining.isLt⟩
      parity := s.parity + if s.remaining.val % 4 = 3 then 1 else 0 }

/-- This is an operational run: no past state is retained by `scanStep`. -/
def scanRun {U : ℕ} : ℕ → ScanState U → ScanState U
  | 0, s => s
  | n + 1, s => scanRun n (scanStep s)

lemma scanRun_halted {U : ℕ} (s : ScanState U)
    (h : s.fuel.val = 0 ∨ s.remaining.val = 0) (n : ℕ) : scanRun n s = s := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [scanRun, scanStep, dif_pos h] using ih

lemma scanRun_parity {U : ℕ} (n : ℕ) (s : ScanState U)
    (hn : s.fuel.val ≤ n) :
    (scanRun n s).parity = parityScan s.fuel.val s.remaining.val s.parity := by
  induction n generalizing s with
  | zero =>
    have hf : s.fuel.val = 0 := by omega
    simp [scanRun, hf, parityScan]
  | succ n ih =>
    by_cases hh : s.fuel.val = 0 ∨ s.remaining.val = 0
    · rw [scanRun_halted s hh]
      rcases hh with hf | hr
      · simp [hf, parityScan]
      · cases hf : s.fuel.val <;> simp [hf, hr, parityScan]
    · have hf : s.fuel.val ≠ 0 := fun h => hh (Or.inl h)
      have hr : s.remaining.val ≠ 0 := fun h => hh (Or.inr h)
      obtain ⟨f, hf'⟩ := Nat.exists_eq_succ_of_ne_zero hf
      obtain ⟨r, hr'⟩ := Nat.exists_eq_succ_of_ne_zero hr
      rw [scanRun, ih (scanStep s) (by simp only [scanStep, dif_neg hh]; omega)]
      simp only [scanStep, dif_neg hh]
      rw [hf', hr', parityScan]
      congr 2 <;> omega

/-- Initialization has only the magnitude and the one-bit parity register. -/
def initialState (U k : ℕ) (hk : k ≤ U) : ScanState U where
  fuel := ⟨k + 1, by omega⟩
  remaining := ⟨k, by omega⟩
  parity := 0

lemma initialState_correct (U k : ℕ) (hk : k ≤ U) :
    (scanRun (U + 1) (initialState U k hk)).parity =
      (adjacentOnesCount k : ZMod 2) := by
  rw [scanRun_parity _ _ (by simp [initialState]; omega)]
  simpa [initialState, adjacentOnesCount] using parityScan_eq (k + 1) k 0

/-- A binary register holding a natural below `n` needs this many bits. -/
def registerBits (n : ℕ) : ℕ := Nat.log 2 n + 1

lemma lt_two_pow_registerBits (n : ℕ) : n < 2 ^ registerBits n :=
  Nat.lt_pow_succ_log_self (by decide) n

/-- Includes every live scan register, with one additional parity bit. -/
def evaluatorBits (U : ℕ) : ℕ :=
  registerBits (U + 2) + registerBits (U + 1) + 1

lemma card_scanState (U : ℕ) :
    Fintype.card (ScanState U) = (U + 2) * (U + 1) * 2 := by
  let e : ScanState U ≃ Fin (U + 2) × Fin (U + 1) × ZMod 2 :=
    { toFun := fun s => (s.fuel, s.remaining, s.parity)
      invFun := fun s => ⟨s.1, s.2.1, s.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e]
  simp [Fintype.card_prod, ZMod.card, Nat.mul_assoc]

lemma evaluator_space_bound (U : ℕ) :
    Fintype.card (ScanState U) ≤ 2 ^ evaluatorBits U := by
  rw [card_scanState]
  unfold evaluatorBits
  rw [pow_add, pow_add]
  have h₁ := (lt_two_pow_registerBits (U + 2)).le
  have h₂ := (lt_two_pow_registerBits (U + 1)).le
  simpa using Nat.mul_le_mul (Nat.mul_le_mul h₁ h₂) (le_refl 2)

/-- The evaluator is correct for every signed input in the final promised range.
The sign needs no register, since the target is even. -/
theorem witness_evaluator (U : ℕ) (k : ℤ) (hk : k.natAbs ≤ U) :
    (weight k : ℝ) = f k ∧
    (scanRun (U + 1) (initialState U k.natAbs hk)).parity =
      (adjacentOnesCount k.natAbs : ZMod 2) ∧
    Fintype.card (ScanState U) ≤ 2 ^ evaluatorBits U :=
  ⟨weight_cast k, initialState_correct U k.natAbs hk, evaluator_space_bound U⟩

end Paper02.WeightEval
