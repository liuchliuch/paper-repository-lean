/-
Copyright (c) 2026. Finite spin systems for the Griffiths-exponent paper.
-/
import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

open Finset BigOperators Classical

namespace Paper09

/-- Ising spin values, realized as `Fin 2` (`0 ↦ -1`, `1 ↦ +1`). -/
abbrev Spin : Type := Fin 2

/-- Real value of a spin: `-1` or `+1`. -/
def spinVal (s : Spin) : ℝ := if s = 0 then -1 else 1

@[simp]
theorem spinVal_zero : spinVal 0 = -1 := by simp [spinVal]

@[simp]
theorem spinVal_one : spinVal 1 = 1 := by
  have h : (1 : Spin) ≠ 0 := by norm_num
  simp [spinVal, h]

theorem spinVal_sq (s : Spin) : spinVal s * spinVal s = 1 := by
  rcases s with ⟨n, hn⟩
  have : n = 0 ∨ n = 1 := by omega
  rcases this with h | h <;> subst h
  · simp [spinVal]
  · have h1 : (⟨1, by omega⟩ : Spin) = 1 := rfl
    simp [spinVal, h1]

/-- A spin configuration on a finite index type. -/
abbrev Config (ι : Type*) := ι → Spin

/-- Hamming distance between two configurations. -/
def hamming {ι : Type*} [Fintype ι] (η η' : Config ι) : ℕ :=
  (univ.filter (fun x => η x ≠ η' x)).card

theorem hamming_self {ι : Type*} [Fintype ι] (η : Config ι) : hamming η η = 0 := by
  simp [hamming]

theorem hamming_comm {ι : Type*} [Fintype ι] (η η' : Config ι) :
    hamming η η' = hamming η' η := by
  simp [hamming, ne_comm]

/-- Dimension exponent `a = (d-1)/d` on naturals, as a real. -/
noncomputable def exponentA (d : ℕ) : ℝ := ((d : ℝ) - 1) / d

theorem exponentA_pos {d : ℕ} (hd : 2 ≤ d) : 0 < exponentA d := by
  have h : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega) hd)
  have h1 : (1 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega) hd)
  unfold exponentA
  apply div_pos
  · linarith
  · exact h

theorem exponentA_lt_one {d : ℕ} (hd : 2 ≤ d) : exponentA d < 1 := by
  have h : (0 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega) hd)
  have h1 : (1 : ℝ) < d := by exact_mod_cast (lt_of_lt_of_le (by omega) hd)
  unfold exponentA
  rw [div_lt_one h]
  linarith

theorem exponentA_eq {d : ℕ} (hd : 0 < d) :
    exponentA d = 1 - 1 / (d : ℝ) := by
  have h : (0 : ℝ) < d := by exact_mod_cast hd
  unfold exponentA
  field_simp [ne_of_gt h]

end Paper09
