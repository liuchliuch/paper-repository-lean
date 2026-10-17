/-
Copyright (c) 2026. The two residue-ring counterexamples in Appendix A.
-/
import Paper06.Incidence
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Order.Floor.Ring

open Real BigOperators

namespace Paper06.ResidueExamples

/-- The actual winning second inputs for a fixed first input. -/
def winningSecondInputs {R : Type*} [Fintype R] [DecidableEq R] [Add R] [Mul R]
    (f g : R → R) (x : R) : Finset R :=
  Finset.univ.filter (fun y => f x + g y = x * y)

/-- Computable version of the winning-pair finset. -/
def winningPairs {R : Type*} [Fintype R] [DecidableEq R] [Add R] [Mul R]
    (f g : R → R) : Finset (R × R) :=
  Finset.univ.filter (fun z => f z.1 + g z.2 = z.1 * z.2)

theorem winningPairs_eq_gameWin {R : Type*} [Fintype R] [DecidableEq R]
    [Add R] [Mul R] (f g : R → R) : winningPairs f g = gameWin f g := by
  ext z
  simp [winningPairs, gameWin]

/-- Appendix A's first response function over the ring `ℤ/4ℤ`. -/
def f4 (x : ZMod 4) : ZMod 4 := if x = 3 then 2 else 0

/-- Appendix A's second response function over the ring `ℤ/4ℤ`. -/
def g4 (y : ZMod 4) : ZMod 4 := if y = 1 then 1 else if y = 3 then 3 else 0

theorem wins4_zero : winningSecondInputs f4 g4 0 = {0, 2} := by decide
theorem wins4_one : winningSecondInputs f4 g4 1 = {0, 1, 3} := by decide
theorem wins4_two : winningSecondInputs f4 g4 2 = {0, 2} := by decide
theorem wins4_three : winningSecondInputs f4 g4 3 = {1, 2, 3} := by decide

/-- Counting actual winning pairs, not an independently stipulated incidence number. -/
theorem incidence4 : Ifg f4 g4 = 10 := by
  rw [Ifg, ← winningPairs_eq_gameWin]
  decide

/-- Appendix A's first response function over the ring `ℤ/6ℤ`. -/
def f6 (x : ZMod 6) : ZMod 6 := if x = 5 then 2 else 0

/-- Appendix A's second response function over the ring `ℤ/6ℤ`. -/
def g6 (y : ZMod 6) : ZMod 6 :=
  if y = 1 then 3 else if y = 2 then 2 else if y = 5 then 5 else 0

theorem wins6_zero : winningSecondInputs f6 g6 0 = {0, 3, 4} := by decide
theorem wins6_one : winningSecondInputs f6 g6 1 = {0, 2, 5} := by decide
theorem wins6_two : winningSecondInputs f6 g6 2 = {0, 3} := by decide
theorem wins6_three : winningSecondInputs f6 g6 3 = {0, 1, 4} := by decide
theorem wins6_four : winningSecondInputs f6 g6 4 = {0, 2, 3} := by decide
theorem wins6_five : winningSecondInputs f6 g6 5 = {1, 2, 4, 5} := by decide

theorem incidence6 : Ifg f6 g6 = 18 := by
  rw [Ifg, ← winningPairs_eq_gameWin]
  decide

/-- The integer field expression in the first example is exactly nine. -/
theorem field_expression4_floor : ⌊(2 : ℝ) * (1 + Real.sqrt 13)⌋ = (9 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  constructor <;> norm_num <;> nlinarith

/-- The integer field expression in the second example is exactly sixteen. -/
theorem field_expression6_floor : ⌊(3 : ℝ) * (1 + Real.sqrt 21)⌋ = (16 : ℤ) := by
  apply Int.floor_eq_iff.mpr
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  constructor <;> norm_num <;> nlinarith

/-- The first ring strategy exceeds the field incidence expression. -/
theorem field_bound_fails4 :
    (2 : ℝ) * (1 + Real.sqrt 13) < (Ifg f4 g4 : ℝ) := by
  rw [incidence4]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 13)
  have hn := Real.sqrt_nonneg (13 : ℝ)
  norm_num
  nlinarith

/-- The second ring strategy exceeds the field incidence expression. -/
theorem field_bound_fails6 :
    (3 : ℝ) * (1 + Real.sqrt 21) < (Ifg f6 g6 : ℝ) := by
  rw [incidence6]
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 21)
  have hn := Real.sqrt_nonneg (21 : ℝ)
  norm_num
  nlinarith

/-- Two different slopes fit the same two different graph points over `ℤ/4ℤ`. -/
theorem nonunique_slope4 :
    ∃ y y' x x' : ZMod 4, y ≠ y' ∧ x ≠ x' ∧
      g4 y - g4 y' = x * (y - y') ∧
      g4 y - g4 y' = x' * (y - y') := by
  refine ⟨0, 2, 0, 2, ?_⟩
  decide

/-- The input difference in that pair has no multiplicative inverse. -/
theorem input_difference4_not_invertible :
    ¬ ∃ v : ZMod 4, ((0 : ZMod 4) - 2) * v = 1 := by decide

end Paper06.ResidueExamples
