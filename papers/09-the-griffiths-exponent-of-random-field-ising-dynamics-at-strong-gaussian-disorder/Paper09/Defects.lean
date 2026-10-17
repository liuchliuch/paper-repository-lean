/-
Copyright (c) 2026. Equilibrium shell defects (Lemma 2.3) analytic core.

Finite exponential-moment certificates for the number of shell defects:
`E exp(b k) ≤ exp(n q (exp b - 1))` and `E exp(-b k) ≥ exp(-b n q)`,
together with the algebraic gap bound (2.6).
-/
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open Finset BigOperators Real

namespace Paper09

/-! ## Elementary exponential bounds -/

/-- For `0 ≤ x`, `(1 + x)^n ≤ exp(n x)`. -/
theorem one_add_pow_le_exp (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ n ≤ Real.exp ((n : ℝ) * x) := by
  have hle : (1 + x) ≤ Real.exp x := by
    linarith [Real.add_one_le_exp x]
  have hbase : (1 + x) ^ n ≤ (Real.exp x) ^ n :=
    pow_le_pow_left₀ (add_nonneg (by norm_num) hx) hle n
  rw [Real.exp_nat_mul]
  exact hbase

/-- Same bound with the argument written on the right:
`(1 + x)^n ≤ exp(x * n)`. -/
theorem one_add_pow_le_exp_mul (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    (1 + x) ^ n ≤ Real.exp (x * (n : ℝ)) := by
  have h := one_add_pow_le_exp n x hx
  have key : (n : ℝ) * x = x * (n : ℝ) := by ring
  rw [key] at h
  exact h

/-- Weighted two-point Jensen / AM–GM for `exp`:
`exp(-b q) ≤ 1 - q + q * exp(-b)` for `0 ≤ q ≤ 1`. -/
theorem exp_neg_le_one_sub_add (q b : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Real.exp (-b * q) ≤ (1 - q) + q * Real.exp (-b) := by
  have hgm := Real.geom_mean_le_arith_mean2_weighted
    (w₁ := 1 - q) (w₂ := q) (p₁ := (1 : ℝ)) (p₂ := Real.exp (-b))
    (sub_nonneg.mpr hq1) hq (by norm_num) (le_of_lt (Real.exp_pos (-b)))
    (by ring)
  -- hgm : (1:ℝ) ^ (1 - q) * rexp (-b) ^ q ≤ (1 - q) * 1 + q * rexp (-b)
  have h1 : ((1 : ℝ) ^ (1 - q)) = 1 := one_rpow _
  have h2 : Real.exp (-b) ^ q = Real.exp (-b * q) := (Real.exp_mul (-b) q).symm
  rw [h1, one_mul, h2] at hgm
  have h3 : (1 - q) * (1 : ℝ) + q * Real.exp (-b) = (1 - q) + q * Real.exp (-b) := by
    ring
  rwa [h3] at hgm

/-! ## Binomial exponential moments -/

/-- Binomial expansion of `E[t^K]` for `K ~ Bin(n, q)`:
`∑_{k=0}^n C(n,k) q^k (1-q)^{n-k} t^k = (1 + q (t - 1))^n`. -/
theorem binomial_moment_eq (n : ℕ) (q t : ℝ) :
    ∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * t ^ k
      = (1 + q * (t - 1)) ^ n := by
  have hsum :
      ∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * t ^ k
        = ∑ k ∈ range (n + 1),
            (q * t) ^ k * (1 - q) ^ (n - k) * (n.choose k : ℝ) := by
    apply sum_congr rfl
    intro k _hk
    rw [mul_pow]
    ring
  have h := add_pow (q * t) (1 - q) n
  have hcore : q * t + (1 - q) = 1 + q * (t - 1) := by ring
  rw [hsum, ← h, hcore]

/-- Paper (2.5) upper certificate, binomial form:
`∑ Bin(n,q) weights · exp(b k) ≤ (1 + q (exp b - 1))^n ≤ exp(n q (exp b - 1))`
for `0 ≤ q`, `0 ≤ b`. -/
theorem defect_exp_moment_upper (n : ℕ) (q b : ℝ) (hq : 0 ≤ q) (hb : 0 ≤ b) :
    ∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (b * k)
      ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)) := by
  have hterm : ∀ k ∈ range (n + 1),
      ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (b * k)
        = ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp b ^ k := by
    intro k _hk
    have hk : Real.exp (b * (k : ℝ)) = Real.exp b ^ k := by
      rw [mul_comm b (k : ℝ), Real.exp_nat_mul]
    rw [hk]
  have heq :
      ∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (b * k)
        = (1 + q * (Real.exp b - 1)) ^ n := by
    rw [sum_congr rfl hterm, binomial_moment_eq]
  have hx : 0 ≤ q * (Real.exp b - 1) := by
    have h1 : (0 : ℝ) ≤ Real.exp b - 1 :=
      sub_nonneg.mpr (Real.one_le_exp_iff.mpr hb)
    exact mul_nonneg hq h1
  rw [heq]
  have h := one_add_pow_le_exp n (q * (Real.exp b - 1)) hx
  -- h : (1 + q * (rexp b - 1)) ^ n ≤ rexp (↑n * (q * (rexp b - 1)))
  have key : (n : ℝ) * (q * (Real.exp b - 1))
      = (n : ℝ) * q * (Real.exp b - 1) := by ring
  rw [key] at h
  exact h

/-- Paper (2.5) lower certificate, binomial form:
`exp(-b n q) ≤ (1 + q (exp(-b) - 1))^n = ∑ Bin(n,q) weights · exp(-b k)`
for `0 ≤ q ≤ 1`, `0 ≤ b`. -/
theorem defect_exp_moment_lower (n : ℕ) (q b : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (_hb : 0 ≤ b) :
    Real.exp (-b * (n : ℝ) * q)
      ≤ ∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (-b * k) := by
  have hterm : ∀ k ∈ range (n + 1),
      ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (-b * k)
        = ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (-b) ^ k := by
    intro k _hk
    have hk : Real.exp (-b * (k : ℝ)) = Real.exp (-b) ^ k := by
      rw [mul_comm (-b) (k : ℝ), Real.exp_nat_mul]
    rw [hk]
  have heq :
      ∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (-b * k)
        = (1 + q * (Real.exp (-b) - 1)) ^ n := by
    rw [sum_congr rfl hterm, binomial_moment_eq]
  -- Two-point Jensen: exp(-b q) ≤ 1 - q + q exp(-b) = 1 + q (exp(-b) - 1).
  have ham : Real.exp (-b * q) ≤ (1 - q) + q * Real.exp (-b) :=
    exp_neg_le_one_sub_add q b hq hq1
  have hform : (1 - q) + q * Real.exp (-b) = 1 + q * (Real.exp (-b) - 1) := by
    ring
  rw [hform] at ham
  have hposL : 0 ≤ Real.exp (-b * q) := le_of_lt (Real.exp_pos _)
  have hpow : Real.exp (-b * q) ^ n
      ≤ (1 + q * (Real.exp (-b) - 1)) ^ n :=
    pow_le_pow_left₀ hposL ham n
  have hexpn : Real.exp (-b * q) ^ n
      = Real.exp ((n : ℝ) * (-b * q)) := (Real.exp_nat_mul _ _).symm
  have harg : (n : ℝ) * (-b * q) = -b * (n : ℝ) * q := by ring
  rw [hexpn, harg] at hpow
  rw [heq]
  exact hpow

/-- Paper (2.5) combined certificate: both exponential moments of a
`Bin(n,q)` defect count, matching
`E e^{b k} ≤ e^{n q (e^b - 1)}` and `E e^{-b k} ≥ e^{-b n q}`. -/
theorem lemma_2_3_defect_moments (n : ℕ) (q b : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 ≤ b) :
    (∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (b * k)
      ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)))
      ∧
    (Real.exp (-b * (n : ℝ) * q)
      ≤ ∑ k ∈ range (n + 1),
        ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (-b * k)) :=
  ⟨defect_exp_moment_upper n q b hq hb,
   defect_exp_moment_lower n q b hq hq1 hb⟩

/-! ## Moment-generating and Jensen forms -/

/-- Convexity of `x ↦ exp(c x)` on `ℝ`. -/
theorem convexOn_exp_mul (c : ℝ) :
    ConvexOn ℝ Set.univ (fun x => Real.exp (c * x)) := by
  have h := convexOn_exp.comp_linearMap (c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
  have heq : (⇑(c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) : ℝ → ℝ) = fun x => c * x := by
    funext x
    simp [LinearMap.smul_apply, smul_eq_mul]
  have hcomp :
      (Real.exp ∘ ⇑(c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)))
        = fun x => Real.exp (c * x) := by
    rw [heq]
    rfl
  have hpre :
      (⇑(c • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) ⁻¹' Set.univ) = (Set.univ : Set ℝ) := by
    simp
  rw [hcomp, hpre] at h
  exact h

/-- Jensen for `x ↦ exp(-b x)` against a finitely supported probability weight:
`E exp(-b k) ≥ exp(-b E k)`. -/
theorem jensen_exp_neg {ι : Type*} (t : Finset ι) (w : ι → ℝ) (k : ι → ℝ) (b : ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1) :
    Real.exp (-b * ∑ i ∈ t, w i * k i) ≤ ∑ i ∈ t, w i * Real.exp (-b * k i) := by
  have hsum := convexOn_exp.map_sum_le hw hw1
    (fun i _ => Set.mem_univ (-(b * k i)))
  -- hsum : rexp (∑ i ∈ t, w i • (-(b * k i))) ≤ ∑ i ∈ t, w i • rexp (-(b * k i))
  have hL : ∑ i ∈ t, (w i : ℝ) • (-(b * k i)) = -b * ∑ i ∈ t, w i * k i := by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro i _hi
    rw [smul_eq_mul]
    ring
  have hR : ∑ i ∈ t, (w i : ℝ) • Real.exp (-(b * k i))
      = ∑ i ∈ t, w i * Real.exp (-b * k i) := by
    apply sum_congr rfl
    intro i _hi
    rw [smul_eq_mul, ← neg_mul]
  rw [hL, hR] at hsum
  exact hsum

/-- Upper MGF form: if `E[s^k] ≤ (1 + q(s-1))^n` for all `s ≥ 1`,
then `E exp(b k) ≤ exp(n q (exp b - 1))`. -/
theorem defect_exp_moment_upper_of_mgf (n : ℕ) (q b : ℝ)
    (hq : 0 ≤ q) (hb : 0 ≤ b)
    {ι : Type*} (t : Finset ι) (w : ι → ℝ) (k : ι → ℕ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hmgf : ∀ s : ℝ, 1 ≤ s →
      ∑ i ∈ t, w i * s ^ (k i) ≤ (1 + q * (s - 1)) ^ n) :
    ∑ i ∈ t, w i * Real.exp (b * (k i : ℝ))
      ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)) := by
  have hb1 : 1 ≤ Real.exp b := Real.one_le_exp_iff.mpr hb
  have hE : ∑ i ∈ t, w i * Real.exp (b * (k i : ℝ))
      = ∑ i ∈ t, w i * Real.exp b ^ (k i) := by
    apply sum_congr rfl
    intro i _hi
    have h : Real.exp (b * (k i : ℝ)) = Real.exp b ^ (k i) := by
      rw [mul_comm b (k i : ℝ), Real.exp_nat_mul]
    rw [h]
  have h := hmgf (Real.exp b) hb1
  have hx : 0 ≤ q * (Real.exp b - 1) :=
    mul_nonneg hq (sub_nonneg.mpr hb1)
  have hchain : (1 + q * (Real.exp b - 1)) ^ n
      ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)) := by
    have h2 := one_add_pow_le_exp n (q * (Real.exp b - 1)) hx
    have key : (n : ℝ) * (q * (Real.exp b - 1))
        = (n : ℝ) * q * (Real.exp b - 1) := by ring
    rw [key] at h2
    exact h2
  rw [hE]
  exact le_trans h hchain

/-- Lower Jensen form: if `E k ≤ n q` then `E exp(-b k) ≥ exp(-b n q)`
for `0 ≤ b`, `0 ≤ q`. -/
theorem defect_exp_moment_lower_jensen (n : ℕ) (q b : ℝ)
    (hb : 0 ≤ b) (_hq : 0 ≤ q)
    {ι : Type*} (t : Finset ι) (w : ι → ℝ) (k : ι → ℝ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hw1 : ∑ i ∈ t, w i = 1)
    (hEk : ∑ i ∈ t, w i * k i ≤ (n : ℝ) * q) :
    Real.exp (-b * (n : ℝ) * q)
      ≤ ∑ i ∈ t, w i * Real.exp (-b * k i) := by
  have hj := jensen_exp_neg t w k b hw hw1
  have hmono : Real.exp (-b * (n : ℝ) * q)
      ≤ Real.exp (-b * ∑ i ∈ t, w i * k i) := by
    have harg : -b * (n : ℝ) * q ≤ -b * ∑ i ∈ t, w i * k i := by
      have hmul : -b * (n : ℝ) * q = -b * ((n : ℝ) * q) := by ring
      rw [hmul]
      exact mul_le_mul_of_nonpos_left hEk (neg_nonpos.mpr hb)
    exact Real.exp_le_exp.mpr harg
  exact le_trans hmono hj

/-! ## Algebraic gap bound (2.6) -/

/-- Paper (2.6): the soft-shell ratio is controlled by the defect moments,
`gap π ≤ gap ν · exp(4A + n q (e^b - 1 + b))`. -/
theorem lemma_2_3_gap_bound
    (n : ℕ) (q b A gapπ gapν Epos Eneg : ℝ)
    (_hq : 0 ≤ q) (_hb : 0 ≤ b) (_hA : 0 ≤ A)
    (hgapν : 0 ≤ gapν)
    (hEpos : Epos ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)))
    (hEneg : Real.exp (-b * (n : ℝ) * q) ≤ Eneg)
    (hEneg_pos : 0 < Eneg)
    (hsoft : gapπ ≤ gapν * Real.exp (4 * A) * (Epos / Eneg)) :
    gapπ ≤ gapν * Real.exp (4 * A + (n : ℝ) * q * (Real.exp b - 1 + b)) := by
  have hU : 0 < Real.exp ((n : ℝ) * q * (Real.exp b - 1)) := Real.exp_pos _
  have hL : 0 < Real.exp (-b * (n : ℝ) * q) := Real.exp_pos _
  have hdiv : Epos / Eneg
      ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)) / Real.exp (-b * (n : ℝ) * q) := by
    have h1 : Epos / Eneg
        ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)) / Eneg :=
      div_le_div_of_nonneg_right hEpos (le_of_lt hEneg_pos)
    have h2 : Real.exp ((n : ℝ) * q * (Real.exp b - 1)) / Eneg
        ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)) / Real.exp (-b * (n : ℝ) * q) :=
      div_le_div_of_nonneg_left (le_of_lt hU) hL hEneg
    exact le_trans h1 h2
  have hquot :
      Real.exp ((n : ℝ) * q * (Real.exp b - 1)) / Real.exp (-b * (n : ℝ) * q)
        = Real.exp ((n : ℝ) * q * (Real.exp b - 1) - (-b * (n : ℝ) * q)) := by
    rw [Real.exp_sub]
  have harg :
      (n : ℝ) * q * (Real.exp b - 1) - (-b * (n : ℝ) * q)
        = (n : ℝ) * q * (Real.exp b - 1 + b) := by ring
  have hdiv' : Epos / Eneg
      ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1 + b)) := by
    rw [hquot, harg] at hdiv
    exact hdiv
  have hmul : gapν * Real.exp (4 * A) * (Epos / Eneg)
      ≤ gapν * Real.exp (4 * A) * Real.exp ((n : ℝ) * q * (Real.exp b - 1 + b)) :=
    mul_le_mul_of_nonneg_left hdiv' (mul_nonneg hgapν (le_of_lt (Real.exp_pos _)))
  have hsoft' : gapπ ≤ gapν * Real.exp (4 * A)
      * Real.exp ((n : ℝ) * q * (Real.exp b - 1 + b)) :=
    le_trans hsoft hmul
  have hcombine :
      gapν * Real.exp (4 * A) * Real.exp ((n : ℝ) * q * (Real.exp b - 1 + b))
        = gapν * Real.exp (4 * A + (n : ℝ) * q * (Real.exp b - 1 + b)) :=
    by rw [mul_assoc, ← Real.exp_add]
  rw [hcombine] at hsoft'
  exact hsoft'

/-- Convenience form of (2.6) with the binomial defect moments already applied. -/
theorem lemma_2_3_gap_bound_binomial
    (n : ℕ) (q b A gapπ gapν : ℝ)
    (hq : 0 ≤ q) (hq1 : q ≤ 1) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hgapν : 0 ≤ gapν)
    (hsoft : gapπ ≤ gapν * Real.exp (4 * A)
      * ((∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (b * k))
      / (∑ k ∈ range (n + 1),
          ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (-b * k)))) :
    gapπ ≤ gapν * Real.exp (4 * A + (n : ℝ) * q * (Real.exp b - 1 + b)) := by
  set Epos := ∑ k ∈ range (n + 1),
      ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (b * k) with hEpos
  set Eneg := ∑ k ∈ range (n + 1),
      ((n.choose k : ℝ) * q ^ k * (1 - q) ^ (n - k)) * Real.exp (-b * k) with hEneg
  have hmom := lemma_2_3_defect_moments n q b hq hq1 hb
  have hEpos_le : Epos ≤ Real.exp ((n : ℝ) * q * (Real.exp b - 1)) :=
    hmom.1
  have hEneg_ge : Real.exp (-b * (n : ℝ) * q) ≤ Eneg := hmom.2
  have hEneg_pos : 0 < Eneg :=
    lt_of_lt_of_le (Real.exp_pos _) hEneg_ge
  exact lemma_2_3_gap_bound n q b A gapπ gapν Epos Eneg
    hq hb hA hgapν hEpos_le hEneg_ge hEneg_pos hsoft

end Paper09
