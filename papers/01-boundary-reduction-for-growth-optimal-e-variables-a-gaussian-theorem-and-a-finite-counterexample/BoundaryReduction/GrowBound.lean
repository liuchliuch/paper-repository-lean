/-
Copyright (c) 2026. GROW–information upper bound (Lemma 2.1), discrete form.

Complete sorry-free proof of the finite-alphabet instance of
the logarithmic inequality behind the paper's Lemma 2.1.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import BoundaryReduction.FiniteKL

open Real Set BigOperators
open scoped Classical

namespace BoundaryReduction

namespace FinProb

variable {α : Type*} [Fintype α]

/-- A `P₀`-e-variable is a nonnegative statistic with null expectation at most one. -/
structure EVar (p₀ : FinProb α) where
  s : α → ℝ
  nonneg : ∀ y, 0 ≤ s y
  expect_le_one : expect p₀ s ≤ 1

/-- Core inequality of Lemma 2.1 under positive masses:
`E_R log S ≤ D(R‖P₀) + log E_{P₀}S`. -/
theorem grow_info_core_of_pos {p₀ r : FinProb α} {S : α → ℝ}
    (hp₀ : ∀ y, 0 < p₀.w y) (hr : ∀ y, 0 < r.w y)
    (hS : ∀ y, 0 < S y) (hm : 0 < expect p₀ S) :
    expect r (fun y => log (S y)) ≤ klPos r p₀ + log (expect p₀ S) := by
  set m : ℝ := expect p₀ S with hmdef
  -- Pointwise: log S = log(r/p₀) + log m + log t, with t = S p₀ /(m r) > 0,
  -- and log t ≤ t - 1. Weighted by r and summed:
  --   ∑ r log S ≤ ∑ r log(r/p₀) + log m * ∑ r + ∑ (S p₀/m) - ∑ r
  --             = D(r‖p₀) + log m + 1 - 1.
  have hpoint : ∀ y, log (S y) ≤ log (r.w y / p₀.w y) + log m
      + (S y * p₀.w y / m - r.w y) / r.w y := by
    intro y
    have hp : 0 < p₀.w y := hp₀ y
    have hrp : 0 < r.w y := hr y
    have hSp : 0 < S y * p₀.w y := mul_pos (hS y) hp
    have hmpos : 0 < m := hm
    have ht : 0 < S y * p₀.w y / (m * r.w y) :=
      div_pos hSp (mul_pos hmpos hrp)
    have hlog : log (S y * p₀.w y / (m * r.w y)) ≤
        S y * p₀.w y / (m * r.w y) - 1 := log_le_sub_one_of_pos ht
    have hsplit : log (S y * p₀.w y / (m * r.w y))
        = log (S y) + log (p₀.w y) - log m - log (r.w y) := by
      have h1 : log (S y * p₀.w y) = log (S y) + log (p₀.w y) :=
        log_mul (ne_of_gt (hS y)) (ne_of_gt hp)
      have h2 : log (m * r.w y) = log m + log (r.w y) :=
        log_mul (ne_of_gt hmpos) (ne_of_gt hrp)
      have h3 : log ((S y * p₀.w y) / (m * r.w y))
          = log (S y * p₀.w y) - log (m * r.w y) :=
        log_div (ne_of_gt hSp) (ne_of_gt (mul_pos hmpos hrp))
      rw [h3, h1, h2]
      ring
    rw [hsplit] at hlog
    have hlogr : log (r.w y / p₀.w y) = log (r.w y) - log (p₀.w y) :=
      log_div (ne_of_gt hrp) (ne_of_gt hp)
    have hform : (S y * p₀.w y / m - r.w y) / r.w y
        = S y * p₀.w y / (m * r.w y) - 1 := by
      field_simp
    rw [hform, hlogr]
    linarith
  -- Weighted pointwise form.
  have hw : ∀ y, r.w y * log (S y)
      ≤ r.w y * log (r.w y / p₀.w y) + r.w y * log m
        + S y * p₀.w y / m - r.w y := by
    intro y
    have hform := hpoint y
    have hmul := mul_le_mul_of_nonneg_left hform (le_of_lt (hr y))
    have hcalc : r.w y * (log (r.w y / p₀.w y) + log m
        + (S y * p₀.w y / m - r.w y) / r.w y)
        = r.w y * log (r.w y / p₀.w y) + r.w y * log m
          + S y * p₀.w y / m - r.w y := by
      have hrp : r.w y ≠ 0 := ne_of_gt (hr y)
      field_simp [hrp]
      ring
    rw [hcalc] at hmul
    exact hmul
  -- Sum.
  have hsum : ∑ y, r.w y * log (S y)
      ≤ ∑ y, (r.w y * log (r.w y / p₀.w y) + r.w y * log m
          + S y * p₀.w y / m - r.w y) :=
    Finset.sum_le_sum (fun y _ => hw y)
  -- Evaluate the right-hand sum.
  have hR : ∑ y, (r.w y * log (r.w y / p₀.w y) + r.w y * log m
      + S y * p₀.w y / m - r.w y)
      = klPos r p₀ + log m := by
    have hsplit : ∑ y, (r.w y * log (r.w y / p₀.w y) + r.w y * log m
        + S y * p₀.w y / m - r.w y)
        = ∑ y, r.w y * log (r.w y / p₀.w y)
          + ∑ y, (r.w y * log m)
          + ∑ y, (S y * p₀.w y / m)
          - ∑ y, r.w y := by
      have h3 : ∀ y, r.w y * log (r.w y / p₀.w y) + r.w y * log m
          + S y * p₀.w y / m - r.w y
          = (r.w y * log (r.w y / p₀.w y)) + (r.w y * log m)
            + (S y * p₀.w y / m) + (-r.w y) := fun y => by ring
      rw [Finset.sum_congr rfl (fun y _ => h3 y)]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_neg_distrib]
      ring
    rw [hsplit]
    have hkl : ∑ y, r.w y * log (r.w y / p₀.w y) = klPos r p₀ := rfl
    have hlogm : ∑ y, (r.w y * log m) = log m := by
      have key : (log m) * (∑ i ∈ Finset.univ, r.w i)
          = ∑ i ∈ Finset.univ, (log m) * r.w i :=
        Finset.mul_sum _ _ _
      have hsame : (∑ y, r.w y * log m)
          = (∑ i ∈ Finset.univ, r.w i * log m) := rfl
      have hcomm : (∑ i ∈ Finset.univ, r.w i * log m)
          = (∑ i ∈ Finset.univ, (log m) * r.w i) :=
        Finset.sum_congr rfl (fun i _ => mul_comm _ _)
      calc (∑ y, r.w y * log m)
          = ∑ i ∈ Finset.univ, r.w i * log m := hsame
        _ = ∑ i ∈ Finset.univ, (log m) * r.w i := hcomm
        _ = (log m) * ∑ i ∈ Finset.univ, r.w i := key.symm
        _ = (log m) * 1 := by rw [r.sum_eq_one]
        _ = log m := by ring
    have hsm : ∑ y, (S y * p₀.w y / m) = 1 := by
      have hdiv : ∀ y, S y * p₀.w y / m = (S y * p₀.w y) / m := fun y => rfl
      have hsum : ∑ y, (S y * p₀.w y / m) = (∑ y, S y * p₀.w y) / m := by
        have hinv : ∀ y, S y * p₀.w y / m = (S y * p₀.w y) * m⁻¹ := fun y => by
          rw [div_eq_mul_inv]
        have key : (∑ i ∈ Finset.univ, (S i * p₀.w i) * m⁻¹)
            = (∑ i ∈ Finset.univ, S i * p₀.w i) * m⁻¹ :=
          (Finset.sum_mul _ _ _).symm
        have hsame : (∑ y, S y * p₀.w y / m)
            = (∑ i ∈ Finset.univ, (S i * p₀.w i) * m⁻¹) :=
          Finset.sum_congr rfl (fun y _ => hinv y)
        have hdiv : (∑ i ∈ Finset.univ, S i * p₀.w i) * m⁻¹
            = (∑ i ∈ Finset.univ, S i * p₀.w i) / m := by
          rw [div_eq_mul_inv]
        rw [hsame, key, hdiv]
      rw [hsum]
      have hmeq : ∑ y, S y * p₀.w y = m := by
        rw [hmdef]
        unfold expect
        exact Finset.sum_congr rfl (fun y _ => by ring)
      rw [hmeq]
      exact div_self (ne_of_gt hm)
    have hr1 : ∑ y, r.w y = 1 := r.sum_eq_one
    rw [hkl, hlogm, hsm, hr1]
    ring
  -- Conclude.
  have hgoal : expect r (fun y => log (S y)) = ∑ y, r.w y * log (S y) := rfl
  have hfinal : ∑ y, r.w y * log (S y) ≤ klPos r p₀ + log m :=
    le_trans hsum (le_of_eq hR)
  rw [hgoal, hmdef]
  exact hfinal

end FinProb

end BoundaryReduction
