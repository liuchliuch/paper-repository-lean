import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
# Register dimensions and source parameters
-/

noncomputable section

namespace Paper25

/-- Source dimension parameters: work qubits `s`, catalyst qubits `c`, steps `T`. -/
structure SourceDims where
  s : ℕ
  c : ℕ
  T : ℕ

namespace SourceDims

variable (D : SourceDims)

/-- Work dimension `K = 2^s`. -/
def K : ℕ := 2 ^ D.s

/-- Catalyst dimension `D_cat = 2^c`. -/
def cat : ℕ := 2 ^ D.c

/-- Total computational dimension `d = K * D_cat`. -/
def d : ℕ := D.K * D.cat

lemma K_pos : 0 < D.K := Nat.two_pow_pos _

lemma cat_pos : 0 < D.cat := Nat.two_pow_pos _

lemma d_pos : 0 < D.d := Nat.mul_pos D.K_pos D.cat_pos

end SourceDims

/-- Real embedding of a natural dimension. -/
abbrev dimR (n : ℕ) : ℝ := (n : ℝ)

lemma dimR_pos {n : ℕ} (hn : 0 < n) : 0 < dimR n := by exact_mod_cast hn

/-- Inverse-polynomial scale. -/
def IsInvPoly (f : ℕ → ℝ) : Prop :=
  ∃ (q : ℕ) (C : ℝ), 0 < C ∧ ∀ n : ℕ, C / ((n : ℝ) + 1) ^ q ≤ |f n|

/-- Polynomial growth. -/
def IsPoly (f : ℕ → ℕ) : Prop :=
  ∃ (q : ℕ) (C : ℝ), 0 < C ∧ ∀ n : ℕ, (f n : ℝ) ≤ C * ((n : ℝ) + 1) ^ q

end Paper25
