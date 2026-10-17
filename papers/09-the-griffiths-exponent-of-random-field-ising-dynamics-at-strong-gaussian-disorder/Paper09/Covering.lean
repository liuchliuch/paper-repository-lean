/-
Copyright (c) 2026. Block covering and local-gap algebra (Lemmas 3.3, A.2).
-/
import Paper09.Coupling
import Paper09.Ising
import Paper09.Dynamics
import Paper09.Main
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open Finset BigOperators Classical Real

noncomputable section

namespace Paper09

/-- The real Hamming distance vanishes on the diagonal. -/
theorem hammingR_self {V : Type*} [Fintype V] (η : V → Spin) :
    hammingR η η = 0 := by
  simp [hammingR, hamming_self]

/-- Number of type-1 centers through a site: `(2s+1)^d`. -/
def type1Count (s d : ℕ) : ℕ := (2 * s + 1) ^ d

theorem type1Count_pos (s d : ℕ) : 0 < type1Count s d := by
  unfold type1Count
  positivity

-- Type-1 size bound is `Paper09.type1_block_size` in `Main.lean`.

/-- Bound (3.6): `W_H ≤ C (log R)^2 + C |B| e^{-R/8}`. -/
def disagreementBound (C R vol : ℝ) : ℝ :=
  C * (log R) ^ 2 + C * vol * exp (- R / 8)

theorem disagreementBound_nonneg {C R vol : ℝ}
    (hC : 0 ≤ C) (_hR : 1 ≤ R) (hvol : 0 ≤ vol) :
    0 ≤ disagreementBound C R vol := by
  unfold disagreementBound
  have h1 : 0 ≤ (log R) ^ 2 := sq_nonneg _
  have h2 : 0 < exp (- R / 8) := exp_pos _
  have h3 : 0 ≤ C * (log R) ^ 2 := mul_nonneg hC h1
  have h4 : 0 ≤ C * vol * exp (- R / 8) := by
    nlinarith [hC, hvol, le_of_lt h2, mul_nonneg hC hvol]
  linarith

/-- Overlap ratio: `Jy * R ≤ C * Iy` implies `Jy / Iy ≤ C / R`. -/
theorem overlap_ratio (Iy Jy R C : ℝ)
    (hI : 0 < Iy) (hR : 0 < R)
    (h : Jy * R ≤ C * Iy) :
    Jy / Iy ≤ C / R := by
  rw [div_le_div_iff₀ hI hR]
  nlinarith

end Paper09
