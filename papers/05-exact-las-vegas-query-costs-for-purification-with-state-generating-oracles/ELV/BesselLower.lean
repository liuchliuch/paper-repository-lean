import ELV.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

/-!
# Proposition 4.2 — one-direction obstruction (arithmetic core)

If only forward (or only inverse) queries are allowed, same-label witnesses
must be mutually orthogonal while each retains a fixed overlap with one
opposite-label witness.  Bessel's inequality then forces the uniform cost
to grow without bound.

We prove the numerical chain: from `|⟨fᵢ, f₊⟩| ≥ 1/2` and `‖fᵢ‖² ≤ C`
one gets `|⟨fᵢ, f₊⟩|² / ‖fᵢ‖² ≥ 1/(4C)`; Bessel gives a sum at most `C`;
hence `N/(4C) ≤ C` and `C ≥ √N / 2`, impossible uniformly in `N`.
-/

noncomputable section

namespace ELV

namespace Bessel

/-- Termwise lower bound used in Proposition 4.2. -/
theorem term_bound (a n C : ℝ) (hC : 0 < C) (hn : 0 < n) (hnC : n ≤ C)
    (ha : (1 / 2 : ℝ) ≤ a) :
    (1 / 4 : ℝ) / C ≤ a ^ 2 / n := by
  have h2 : (1 / 4 : ℝ) ≤ a ^ 2 := by nlinarith [sq_nonneg a, abs_nonneg a]
  rw [div_le_div_iff₀ (by positivity) hn]
  nlinarith

/-- Pure arithmetic form of the Proposition 4.2 contradiction:
    if `N` terms each contribute at least `1/(4C)` and their sum is at most `C`,
    then `C ≥ √N / 2`. -/
theorem prop42_numeric (N : ℕ) (C : ℝ) (hC : 0 < C)
    (h : (N : ℝ) * ((1 / 4 : ℝ) / C) ≤ C) :
    Real.sqrt N / 2 ≤ C := by
  have h3 : (N : ℝ) * ((1 / 4 : ℝ) / C) = ((N : ℝ) / 4) / C := by
    field_simp
  rw [h3] at h
  have h4 : ((N : ℝ) / 4) ≤ C * C := by
    have := (div_le_iff₀ (by positivity : 0 < C)).mp h
    nlinarith
  have hsq : (N : ℝ) / 4 ≤ C ^ 2 := by nlinarith
  have hposN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have hsqr : Real.sqrt ((N : ℝ) / 4) ≤ Real.sqrt (C ^ 2) :=
    Real.sqrt_le_sqrt (by nlinarith)
  have hsplit : Real.sqrt ((N : ℝ) / 4) = Real.sqrt N / 2 := by
    rw [Real.sqrt_div hposN]
    have : Real.sqrt (4 : ℝ) = 2 := by norm_num
    rw [this]
  rw [hsplit] at hsqr
  have hC2 : Real.sqrt (C ^ 2) = C := Real.sqrt_sq (le_of_lt hC)
  rw [hC2] at hsqr
  exact hsqr

/-- For every finite bound `C > 0` there is a cardinality `N` that breaks it. -/
theorem unbounded_obstruction (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, (2 * C) ^ 2 < (N : ℝ) := by
  refine ⟨⌊(2 * C) ^ 2⌋₊ + 1, ?_⟩
  have h := Nat.lt_floor_add_one ((2 * C) ^ 2)
  have h2 : 0 ≤ (2 * C) ^ 2 := sq_nonneg _
  have hle := Nat.floor_le h2
  push_cast
  nlinarith

/-- Combining: the Bessel chain yields unbounded cost (Proposition 4.2). -/
theorem prop42_unbounded (C : ℝ) (hC : 0 < C) :
    ∃ N : ℕ, Real.sqrt N / 2 > C := by
  obtain ⟨N, hN⟩ := unbounded_obstruction C hC
  refine ⟨N, ?_⟩
  have : Real.sqrt ((2 * C) ^ 2) < Real.sqrt (N : ℝ) :=
    Real.sqrt_lt_sqrt (by positivity) hN
  have h2 : Real.sqrt ((2 * C) ^ 2) = 2 * C := by
    rw [Real.sqrt_sq (by positivity)]
  rw [h2] at this
  nlinarith

/-- Free-variable packaging: no finite uniform cost serves all `N`. -/
theorem one_direction_infinite : ∀ C : ℝ, 0 < C → ∃ N : ℕ, Real.sqrt N / 2 > C :=
  prop42_unbounded

end Bessel

end ELV
