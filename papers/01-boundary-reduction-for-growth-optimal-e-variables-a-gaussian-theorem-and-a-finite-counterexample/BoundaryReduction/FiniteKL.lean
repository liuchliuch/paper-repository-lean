/-
Copyright (c) 2026. Finite-alphabet relative entropy facts used by
"Boundary reduction for growth-optimal e-variables".

Complete sorry-free proofs of the discrete identities underwriting
Lemma 2.1, Proposition 3.2 and Lemma A.1.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

open Real Set BigOperators
open scoped Classical

namespace BoundaryReduction

/-- A probability mass function on a finite type: nonnegative weights summing to one. -/
structure FinProb (α : Type*) [Fintype α] where
  w : α → ℝ
  nonneg : ∀ y, 0 ≤ w y
  sum_eq_one : ∑ y, w y = 1

namespace FinProb

variable {α : Type*} [Fintype α]

/-- Expectation of a statistic under `p`. -/
def expect (p : FinProb α) (f : α → ℝ) : ℝ := ∑ y, p.w y * f y

/-- Total variation distance `½ ∑ |p(y) - q(y)|`. -/
noncomputable def tv (p q : FinProb α) : ℝ :=
  (1 / 2 : ℝ) * ∑ y, |p.w y - q.w y|

/-- Finite-alphabet KL divergence `∑ p(y) log (p(y)/q(y))`. -/
noncomputable def klPos (p q : FinProb α) : ℝ :=
  ∑ y, p.w y * log (p.w y / q.w y)

/-- Chi-square divergence `∑ (p(y)-q(y))² / q(y)`. -/
noncomputable def chiSq (p q : FinProb α) : ℝ :=
  ∑ y, (p.w y - q.w y) ^ 2 / q.w y

theorem expect_const (p : FinProb α) (c : ℝ) :
    expect p (fun _ => c) = c := by
  unfold expect
  have key : (∑ i ∈ Finset.univ, p.w i) * c = ∑ i ∈ Finset.univ, p.w i * c :=
    Finset.sum_mul _ _ _
  have hsame : (∑ y, p.w y * c) = (∑ i ∈ Finset.univ, p.w i * c) := rfl
  calc (∑ y, p.w y * c)
      = (∑ i ∈ Finset.univ, p.w i * c) := hsame
    _ = (∑ i ∈ Finset.univ, p.w i) * c := key.symm
    _ = 1 * c := by rw [p.sum_eq_one]
    _ = c := one_mul _

theorem expect_smul (p : FinProb α) (c : ℝ) (f : α → ℝ) :
    expect p (fun y => c * f y) = c * expect p f := by
  unfold expect
  have key : c * (∑ i ∈ Finset.univ, p.w i * f i)
      = ∑ i ∈ Finset.univ, c * (p.w i * f i) :=
    Finset.mul_sum _ _ _
  have h1 : ∀ y, p.w y * (c * f y) = c * (p.w y * f y) := fun y => by ring
  have h2 : (∑ y, p.w y * (c * f y))
      = ∑ i ∈ Finset.univ, c * (p.w i * f i) :=
    calc (∑ y, p.w y * (c * f y))
          = ∑ i ∈ Finset.univ, p.w i * (c * f i) := rfl
        _ = ∑ i ∈ Finset.univ, c * (p.w i * f i) :=
          Finset.sum_congr rfl (fun i _ => h1 i)
  have h3 : c * ∑ y, p.w y * f y = c * ∑ i ∈ Finset.univ, p.w i * f i := rfl
  calc (∑ y, p.w y * (c * f y))
      = ∑ i ∈ Finset.univ, c * (p.w i * f i) := h2
    _ = c * ∑ i ∈ Finset.univ, p.w i * f i := key.symm
    _ = c * ∑ y, p.w y * f y := h3.symm

/-! ### Chain rule -/

theorem klPos_chain_rule {p q r : FinProb α}
    (hq : ∀ y, 0 < q.w y) (hr : ∀ y, 0 < r.w y) :
    klPos p r = klPos p q + expect p (fun y => log (q.w y / r.w y)) := by
  show ∑ y, p.w y * log (p.w y / r.w y)
      = ∑ y, p.w y * log (p.w y / q.w y) + ∑ y, p.w y * log (q.w y / r.w y)
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y hy
  by_cases hp0 : p.w y = 0
  · simp [hp0]
  · have hp_pos : 0 < p.w y := lt_of_le_of_ne (p.nonneg y) (Ne.symm hp0)
    have hdiv : p.w y / r.w y = (p.w y / q.w y) * (q.w y / r.w y) := by
      have hq0 : q.w y ≠ 0 := ne_of_gt (hq y)
      have hr0 : r.w y ≠ 0 := ne_of_gt (hr y)
      field_simp [hq0, hr0, mul_comm, mul_left_comm, mul_assoc]
    rw [hdiv, log_mul (ne_of_gt (div_pos hp_pos (hq y)))
        (ne_of_gt (div_pos (hq y) (hr y))), mul_add]

/-! ### Gibbs' inequality -/

theorem klPos_nonneg {p q : FinProb α} (hq : ∀ y, 0 < q.w y) :
    0 ≤ klPos p q := by
  show 0 ≤ ∑ y, p.w y * log (p.w y / q.w y)
  have hpoint : ∀ y, p.w y - q.w y ≤ p.w y * log (p.w y / q.w y) := by
    intro y
    by_cases hp0 : p.w y = 0
    · have hz : (0 : ℝ) * log (0 / q.w y) = 0 := by rw [zero_mul]
      rw [hp0, hz]
      have : 0 ≤ q.w y := le_of_lt (hq y)
      linarith
    · have hp : 0 < p.w y := lt_of_le_of_ne (p.nonneg y) (Ne.symm hp0)
      have hlog : log (p.w y / q.w y) = - log (q.w y / p.w y) := by
        rw [log_div (ne_of_gt hp) (ne_of_gt (hq y)),
            log_div (ne_of_gt (hq y)) (ne_of_gt hp)]
        ring
      have hqlog : log (q.w y / p.w y) ≤ (q.w y / p.w y) - 1 :=
        log_le_sub_one_of_pos (div_pos (hq y) hp)
      have hge : 1 - q.w y / p.w y ≤ log (p.w y / q.w y) := by
        rw [hlog]
        linarith
      have hmul : p.w y * (1 - q.w y / p.w y) ≤ p.w y * log (p.w y / q.w y) :=
        mul_le_mul_of_nonneg_left hge (le_of_lt hp)
      have hrhs : p.w y * (1 - q.w y / p.w y) = p.w y - q.w y := by
        field_simp
      rw [hrhs] at hmul
      exact hmul
  have hsum : ∑ y, (p.w y - q.w y) ≤ ∑ y, p.w y * log (p.w y / q.w y) :=
    Finset.sum_le_sum (fun y _ => hpoint y)
  have hsumL : ∑ y, (p.w y - q.w y) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_eq_one, q.sum_eq_one]
    ring
  linarith

/-! ### Chi-square upper bound -/

theorem klPos_le_chiSq {p q : FinProb α} (hq : ∀ y, 0 < q.w y) :
    klPos p q ≤ chiSq p q := by
  show (∑ y, p.w y * log (p.w y / q.w y)) ≤ (∑ y, (p.w y - q.w y) ^ 2 / q.w y)
  have hpoint : ∀ y, p.w y * log (p.w y / q.w y) ≤ p.w y ^ 2 / q.w y - p.w y := by
    intro y
    have hqy : 0 < q.w y := hq y
    by_cases hp0 : p.w y = 0
    · have hz : (0 : ℝ) * log (0 / q.w y) = 0 := by rw [zero_mul]
      rw [hp0, hz, zero_pow (by norm_num : (2:ℕ) ≠ 0), zero_div, zero_sub]
      have : 0 ≤ q.w y := le_of_lt hqy
      linarith
    · have hp : 0 < p.w y := lt_of_le_of_ne (p.nonneg y) (Ne.symm hp0)
      have hlog : log (p.w y / q.w y) ≤ (p.w y / q.w y) - 1 :=
        log_le_sub_one_of_pos (div_pos hp hqy)
      have hmul : p.w y * log (p.w y / q.w y) ≤ p.w y * ((p.w y / q.w y) - 1) :=
        mul_le_mul_of_nonneg_left hlog (le_of_lt hp)
      have hrhs : p.w y * ((p.w y / q.w y) - 1) = p.w y ^ 2 / q.w y - p.w y := by
        field_simp
      linarith
  have hsum : ∑ y, p.w y * log (p.w y / q.w y)
      ≤ ∑ y, (p.w y ^ 2 / q.w y - p.w y) :=
    Finset.sum_le_sum (fun y _ => hpoint y)
  have hR : ∑ y, (p.w y ^ 2 / q.w y - p.w y)
      = ∑ y, (p.w y - q.w y) ^ 2 / q.w y := by
    have h1 : ∑ y, (p.w y ^ 2 / q.w y - p.w y) = (∑ y, p.w y ^ 2 / q.w y) - 1 := by
      rw [Finset.sum_sub_distrib, p.sum_eq_one]
    have h2 : ∑ y, (p.w y - q.w y) ^ 2 / q.w y = (∑ y, p.w y ^ 2 / q.w y) - 1 := by
      have hpt : ∀ y, (p.w y - q.w y) ^ 2 / q.w y
          = p.w y ^ 2 / q.w y - 2 * p.w y + q.w y := by
        intro y
        have hqy : 0 < q.w y := hq y
        have hexp : (p.w y - q.w y) ^ 2
            = p.w y ^ 2 - 2 * p.w y * q.w y + q.w y ^ 2 := by ring
        rw [hexp]
        field_simp [hqy.ne', mul_comm, mul_left_comm, mul_assoc]
      have hre : (∑ y, (p.w y - q.w y) ^ 2 / q.w y)
          = ∑ y, (p.w y ^ 2 / q.w y - 2 * p.w y + q.w y) :=
        Finset.sum_congr rfl (fun y _ => hpt y)
      rw [hre]
      have h2a : ∑ y, (p.w y ^ 2 / q.w y - 2 * p.w y + q.w y)
          = (∑ y, p.w y ^ 2 / q.w y) - 2 * (∑ y, p.w y) + (∑ y, q.w y) := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        have key : (2 : ℝ) * (∑ i ∈ Finset.univ, p.w i)
            = ∑ i ∈ Finset.univ, 2 * p.w i :=
          Finset.mul_sum _ _ _
        have h2m : (∑ y, 2 * p.w y) = (∑ i ∈ Finset.univ, 2 * p.w i) := rfl
        rw [← h2m, ← key]
        -- goal is now syntactic `rfl` after the two rewrites
      have hfin : (∑ y, p.w y ^ 2 / q.w y) - 2 * (1 : ℝ) + 1
          = (∑ y, p.w y ^ 2 / q.w y) - 1 := by ring
      calc ∑ y, (p.w y ^ 2 / q.w y - 2 * p.w y + q.w y)
          = (∑ y, p.w y ^ 2 / q.w y) - 2 * (∑ y, p.w y) + (∑ y, q.w y) := h2a
        _ = (∑ y, p.w y ^ 2 / q.w y) - 2 * (1 : ℝ) + (1 : ℝ) := by
            rw [p.sum_eq_one, q.sum_eq_one]
        _ = (∑ y, p.w y ^ 2 / q.w y) - 1 := hfin
    rw [h1, h2]
  rw [← hR]
  exact hsum

/-! ### Expectation versus total variation -/

theorem abs_expect_sub_le {p q : FinProb α} {f : α → ℝ} {L : ℝ}
    (hf : ∀ y, |f y| ≤ L) : |expect p f - expect q f| ≤ L * ∑ y, |p.w y - q.w y| := by
  have h : expect p f - expect q f = ∑ y, (p.w y - q.w y) * f y := by
    show (∑ y, p.w y * f y) - (∑ y, q.w y * f y) = ∑ y, (p.w y - q.w y) * f y
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  rw [h]
  have hle : |∑ y, (p.w y - q.w y) * f y| ≤ ∑ y, |(p.w y - q.w y) * f y| :=
    Finset.abs_sum_le_sum_abs _ _
  have hL : ∑ y, |p.w y - q.w y| * |f y| ≤ ∑ y, |p.w y - q.w y| * L :=
    Finset.sum_le_sum (fun y _ => mul_le_mul_of_nonneg_left (hf y) (abs_nonneg _))
  have hL' : ∑ y, |p.w y - q.w y| * L = L * ∑ y, |p.w y - q.w y| := by
    have key : L * (∑ i ∈ Finset.univ, |p.w i - q.w i|)
        = ∑ i ∈ Finset.univ, L * |p.w i - q.w i| :=
      Finset.mul_sum _ _ _
    have hsame : (∑ y, |p.w y - q.w y| * L)
        = (∑ i ∈ Finset.univ, |p.w i - q.w i| * L) := rfl
    calc (∑ y, |p.w y - q.w y| * L)
        = ∑ i ∈ Finset.univ, |p.w i - q.w i| * L := hsame
      _ = ∑ i ∈ Finset.univ, L * |p.w i - q.w i| :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      _ = L * ∑ i ∈ Finset.univ, |p.w i - q.w i| := key.symm
      _ = L * ∑ y, |p.w y - q.w y| := rfl
  calc |∑ y, (p.w y - q.w y) * f y|
      ≤ ∑ y, |(p.w y - q.w y) * f y| := hle
    _ = ∑ y, |p.w y - q.w y| * |f y| :=
        Finset.sum_congr rfl (fun y _ => abs_mul _ _)
    _ ≤ ∑ y, |p.w y - q.w y| * L := hL
    _ = L * ∑ y, |p.w y - q.w y| := hL'

theorem abs_expect_le_two_mul_tv {p q : FinProb α} {g : α → ℝ} {L : ℝ}
    (hg : ∀ y, |g y| ≤ L) (hqg : expect q g = 0) :
    |expect p g| ≤ 2 * L * tv p q := by
  have h := abs_expect_sub_le (f := g) (L := L) (p := p) (q := q) hg
  rw [hqg, sub_zero] at h
  show |expect p g| ≤ 2 * L * ((1 / 2 : ℝ) * ∑ y, |p.w y - q.w y|)
  nlinarith

end FinProb

end BoundaryReduction
