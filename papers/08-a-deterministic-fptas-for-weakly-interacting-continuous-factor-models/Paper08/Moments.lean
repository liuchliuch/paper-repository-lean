import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Paper08.Basic

/-!
# Moments and the logarithmic-coefficient recurrence (2.13)–(2.15)

Formal core of the conversion from moments `M_j(B)` to logarithmic
coefficients `d_j(B)`:

`d_j = M_j - (1/j) ∑_{i=1}^{j-1} i · d_i · M_{j-i}`.

We package the recurrence as a predicate `Recurrence M d`, which is the
exact identity (2.15) together with `d_0 = 0`.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace Moments

/-- The exact recurrence (2.15) and the normalisation `d_0 = 0`. -/
def Recurrence (M d : ℕ → ℝ) : Prop :=
  d 0 = 0 ∧
  ∀ j : ℕ, 1 ≤ j →
    d j = M j - (1 / (j : ℝ)) * (∑ i ∈ Finset.range j, (i : ℝ) * d i * M (j - i))

/-- `d_0 = 0`. -/
lemma d_zero {M d : ℕ → ℝ} (h : Recurrence M d) : d 0 = 0 := h.1

/-- First coefficient: `d_1 = M_1`. -/
lemma d_one {M d : ℕ → ℝ} (h : Recurrence M d) : d 1 = M 1 := by
  have := h.2 1 (by norm_num)
  have hsum : (∑ i ∈ Finset.range 1, ((i:ℝ) * d i * M (1 - i))) = 0 := by
    rw [Finset.range_one, Finset.sum_singleton]
    rw [d_zero h]
    norm_num
  rw [hsum, mul_zero, sub_zero] at this
  exact this

/-- Second coefficient: `d_2 = M_2 - (1/2) d_1 M_1`. -/
lemma d_two {M d : ℕ → ℝ} (h : Recurrence M d) :
    d 2 = M 2 - (1 / 2) * (d 1 * M 1) := by
  have := h.2 2 (by norm_num)
  have hsum : (∑ i ∈ Finset.range 2, ((i:ℝ) * d i * M (2 - i)))
      = (1:ℝ) * d 1 * M 1 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    rw [d_zero h]
    norm_num
  rw [hsum] at this
  ring_nf at this ⊢
  linarith

/-- The recurrence uniquely determines `d` from `M`. -/
lemma recurrence_unique {M d₁ d₂ : ℕ → ℝ}
    (h1 : Recurrence M d₁) (h2 : Recurrence M d₂) (j : ℕ) :
    d₁ j = d₂ j := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      rw [h1.1, h2.1]
    · rw [h1.2 j hj, h2.2 j hj]
      congr 1
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      have hi' : i < j := Finset.mem_range.mp hi
      rw [ih i hi']

/-- Exact arithmetic: `D_0 = 2^{P s + r J} s!` is the common denominator
bound of §4. -/
def denomBound (P s r J : ℕ) : ℕ := 2 ^ (P * s + r * J) * Nat.factorial s

lemma denomBound_pos (P s r J : ℕ) : 1 ≤ denomBound P s r J := by
  unfold denomBound
  have h1 : 0 < 2 ^ (P * s + r * J) :=
    pow_pos (by decide : (0:ℕ) < 2) _
  have h2 : 0 < Nat.factorial s := Nat.factorial_pos s
  exact Nat.succ_le_of_lt (Nat.mul_pos h1 h2)

/-- Primitive moment error propagation through (2.13): at most `4^s` terms
with factorial weights of absolute value at most `1`, so a primitive error
`τ_0` produces moment error at most `4^s τ_0`. -/
lemma moment_error_le {ι : Type*} (S : Finset ι) (w I Ihat : ι → ℝ)
    (s : ℕ) (τ : ℝ) (hτ : 0 ≤ τ) (hcard : S.card ≤ 4 ^ s)
    (hw : ∀ i ∈ S, |w i| ≤ 1) (herr : ∀ i ∈ S, |Ihat i - I i| ≤ τ) :
    |(∑ i ∈ S, w i * Ihat i) - ∑ i ∈ S, w i * I i| ≤ (4 : ℝ) ^ s * τ := by
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ i ∈ S, |w i * Ihat i - w i * I i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ S, τ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [← mul_sub, abs_mul]
      exact (mul_le_mul (hw i hi) (herr i hi) (abs_nonneg _) (by norm_num)).trans_eq
        (one_mul τ)
    _ = S.card * τ := by simp
    _ ≤ (4 : ℝ) ^ s * τ :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hτ

/-- Stability input of Lemma 4.1: `ξ ≤ F^{-s}` is the accuracy required
of the moments. -/
def StabilityHyp (F : ℝ) (s : ℕ) (ξ : ℝ) : Prop :=
  ξ ≤ F ^ (-(s : ℝ))

end Moments
end Paper08
