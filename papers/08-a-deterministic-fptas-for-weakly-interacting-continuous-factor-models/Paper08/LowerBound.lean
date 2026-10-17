import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.Convex.Mul
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic
import Paper08.Basic
import Paper08.Appendix
import Paper08.FPTAS

/-!
# Proposition B.1 — deterministic value-query scale

Analytic and combinatorial core of the fooling-function lower bound (Appendix B).

* Bump `p(t) = 16 t² (1-t)²`: endpoints, derivative bounds, `∫₀¹ p = 8/15`.
* Product bump `φ` and mass `J_r = (8/15)^r`.
* Constants `a₀ = min{U-1, K/(8√r), 1}` and `c₀ = a₀ J_r / 6`.
* Grid counting (at least half the cells stay unmarked) and the mass bound
  `μ_e ≥ c₀ (N_e+1)^{-1/r}` of (B.2).
* Jensen / power-mean step for `x ↦ x^{-1/r}`.
* Logarithmic accuracy step `log(1+x) ≥ x/U`.
* Algebraic combination yielding the query lower bound (B.1).
* Converse surrogate inequalities of the upper bound.

This file provides the scalar analytic lemmas. The companion modules
`LowerBoundSmooth`, `LowerBoundGrid`, `LowerBoundLip`, and `LowerBoundMass`
construct and prove the actual global C¹ fooling functions, while
`LowerBoundAdaptive.prop_B1_adaptive` proves the adaptive algorithm lower bound.
-/

noncomputable section

open scoped Real BigOperators
open MeasureTheory

namespace Paper08
namespace LowerBound

open Appendix FPTAS

/-- The exponent `-1/r` used throughout Proposition B.1. -/
def negInvR (r : ℕ) : ℝ := -((1:ℝ) / r)

lemma negInvR_eq (r : ℕ) : negInvR r = -((1:ℝ) / r) := rfl

lemma negInvR_nonpos (r : ℕ) : negInvR r ≤ 0 := by
  unfold negInvR
  by_cases h : r = 0
  · subst h; norm_num
  · have : (0:ℝ) < r := by positivity
    have : 0 ≤ (1:ℝ) / r := by positivity
    linarith

lemma negInvR_mul_r (r : ℕ) (hr : 0 < (r : ℝ)) : negInvR r * r = -1 := by
  unfold negInvR
  field_simp

/-! ## 1. The one-dimensional bump `p(t) = 16 t² (1-t)²` -/

lemma bump_eq_expand (t : ℝ) : bump t = 16 * t ^ 2 - 32 * t ^ 3 + 16 * t ^ 4 := by
  unfold bump
  ring

lemma bump_zero : bump 0 = 0 := by
  unfold bump
  norm_num

lemma bump_one : bump 1 = 0 := by
  unfold bump
  norm_num

lemma hasDerivAt_bump_expand (t : ℝ) :
    HasDerivAt (fun s : ℝ => 16 * s ^ 2 - 32 * s ^ 3 + 16 * s ^ 4)
      (32 * t - 96 * t ^ 2 + 64 * t ^ 3) t := by
  have d2 : HasDerivAt (fun s : ℝ => s ^ 2) (2 * t) t := by
    convert hasDerivAt_pow (n := 2) t using 1
    norm_num
  have d3 : HasDerivAt (fun s : ℝ => s ^ 3) (3 * t ^ 2) t := by
    convert hasDerivAt_pow (n := 3) t using 1
  have d4 : HasDerivAt (fun s : ℝ => s ^ 4) (4 * t ^ 3) t := by
    convert hasDerivAt_pow (n := 4) t using 1
  have c2 : HasDerivAt (fun s : ℝ => 16 * s ^ 2) (16 * (2 * t)) t :=
    d2.const_mul 16
  have c3 : HasDerivAt (fun s : ℝ => -(32 * s ^ 3)) (-(32 * (3 * t ^ 2))) t :=
    (d3.const_mul 32).neg
  have c4 : HasDerivAt (fun s : ℝ => 16 * s ^ 4) (16 * (4 * t ^ 3)) t :=
    d4.const_mul 16
  have h := (c2.add c3).add c4
  convert h using 1
  ring

/-- Derivative of the bump in expanded form. -/
lemma deriv_bump_expand (t : ℝ) : deriv bump t = 32 * t - 96 * t ^ 2 + 64 * t ^ 3 := by
  have h : deriv (fun s : ℝ => 16 * s ^ 2 - 32 * s ^ 3 + 16 * s ^ 4) t
      = 32 * t - 96 * t ^ 2 + 64 * t ^ 3 :=
    (hasDerivAt_bump_expand t).deriv
  have e : bump = fun s : ℝ => 16 * s ^ 2 - 32 * s ^ 3 + 16 * s ^ 4 := by
    funext s
    exact bump_eq_expand s
  rw [e]
  exact h

/-- Derivative of the bump in factored form: `p'(t) = 32 t (1-t) (1-2t)`. -/
lemma deriv_bump_eq (t : ℝ) : deriv bump t = 32 * t * (1 - t) * (1 - 2 * t) := by
  rw [deriv_bump_expand]
  ring

lemma bump_deriv_zero : deriv bump 0 = 0 := by
  rw [deriv_bump_eq]
  ring

lemma bump_deriv_one : deriv bump 1 = 0 := by
  rw [deriv_bump_eq]
  ring

/-- `|p'(t)| ≤ 8` on `[0,1]` (paper: `|p'| ≤ 8`). -/
lemma bump_deriv_abs_le_eight {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    |deriv bump t| ≤ 8 := by
  have h1 : 0 ≤ t := ht.1
  have h2 : t ≤ 1 := ht.2
  have h3 : 0 ≤ (1 - t : ℝ) := by linarith
  have h4 : |(1 - 2 * t : ℝ)| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have h5 : t * (1 - t) ≤ 1 / 4 := by
    have : 0 ≤ (2 * t - 1) ^ 2 := sq_nonneg _
    nlinarith
  have h6 : 0 ≤ t * (1 - t) := mul_nonneg h1 h3
  have h7 : |t * (1 - t) * (1 - 2 * t)| ≤ 1 / 4 := by
    rw [abs_mul, abs_mul, abs_of_nonneg h1, abs_of_nonneg h3]
    calc t * (1 - t) * |1 - 2 * t| ≤ t * (1 - t) * 1 :=
          mul_le_mul_of_nonneg_left h4 h6
      _ = t * (1 - t) := by ring
      _ ≤ 1 / 4 := h5
  rw [deriv_bump_eq]
  have h8 : |(32:ℝ) * (t * (1 - t) * (1 - 2 * t))|
      = 32 * |t * (1 - t) * (1 - 2 * t)| := by
    rw [abs_mul]
    norm_num
  have h9 : |(32:ℝ) * t * (1 - t) * (1 - 2 * t)|
      = |(32:ℝ) * (t * (1 - t) * (1 - 2 * t))| := by
    congr 1
    ring
  rw [h9, h8]
  have h10 : (32:ℝ) * (1 / 4) = 8 := by norm_num
  calc 32 * |t * (1 - t) * (1 - 2 * t)| ≤ 32 * (1 / 4) :=
        mul_le_mul_of_nonneg_left h7 (by norm_num)
    _ = 8 := h10

/-- `∫₀¹ p = 8/15` for the bump of Proposition B.1. -/
lemma bump_integral_eq : ∫ x in (0:ℝ)..1, bump x = 8 / 15 := by
  have heq : ∀ x ∈ Set.uIcc (0:ℝ) 1,
      bump x = (fun x : ℝ => 16 * x ^ 2 - 32 * x ^ 3 + 16 * x ^ 4) x := by
    intro x _
    exact bump_eq_expand x
  rw [intervalIntegral.integral_congr heq]
  have i1 : IntervalIntegrable (fun x : ℝ => (16:ℝ) * x ^ 2) volume 0 1 :=
    (continuous_const.mul (continuous_pow 2)).intervalIntegrable 0 1
  have i2 : IntervalIntegrable (fun x : ℝ => (32:ℝ) * x ^ 3) volume 0 1 :=
    (continuous_const.mul (continuous_pow 3)).intervalIntegrable 0 1
  have i3 : IntervalIntegrable (fun x : ℝ => (16:ℝ) * x ^ 4) volume 0 1 :=
    (continuous_const.mul (continuous_pow 4)).intervalIntegrable 0 1
  have i12 : IntervalIntegrable
      (fun x : ℝ => (16:ℝ) * x ^ 2 - (32:ℝ) * x ^ 3) volume 0 1 := i1.sub i2
  rw [intervalIntegral.integral_add i12 i3, intervalIntegral.integral_sub i1 i2]
  have p2 : (∫ x in (0:ℝ)..1, (16:ℝ) * x ^ 2)
      = 16 * ((1:ℝ) ^ 3 - 0 ^ 3) / 3 := by
    rw [intervalIntegral.integral_const_mul]
    have h := integral_pow (a := (0:ℝ)) (b := 1) (n := 2)
    norm_num at h ⊢
  have p3 : (∫ x in (0:ℝ)..1, (32:ℝ) * x ^ 3)
      = 32 * ((1:ℝ) ^ 4 - 0 ^ 4) / 4 := by
    rw [intervalIntegral.integral_const_mul]
    have h := integral_pow (a := (0:ℝ)) (b := 1) (n := 3)
    norm_num at h ⊢
  have p4 : (∫ x in (0:ℝ)..1, (16:ℝ) * x ^ 4)
      = 16 * ((1:ℝ) ^ 5 - 0 ^ 5) / 5 := by
    rw [intervalIntegral.integral_const_mul]
    have h := integral_pow (a := (0:ℝ)) (b := 1) (n := 4)
    norm_num at h ⊢
  rw [p2, p3, p4]
  norm_num

lemma bump_integral_pos : 0 < ∫ x in (0:ℝ)..1, bump x := by
  rw [bump_integral_eq]
  norm_num

/-! ## 2. Product bump `φ` and mass `J_r = (8/15)^r` -/

/-- `φ(u) = ∏_{j=1}^r p(u_j)` on `ℝ^r`. -/
def phi (r : ℕ) (u : Fin r → ℝ) : ℝ := ∏ j : Fin r, bump (u j)

lemma phi_nonneg (r : ℕ) (u : Fin r → ℝ) : 0 ≤ phi r u := by
  unfold phi
  exact Finset.prod_nonneg fun j _ => bump_nonneg (u j)

lemma phi_le_one (r : ℕ) (u : Fin r → ℝ) (hu : ∀ j, u j ∈ Set.Icc (0:ℝ) 1) :
    phi r u ≤ 1 := by
  unfold phi
  refine Finset.prod_le_one (fun j _ => bump_nonneg (u j)) ?_
  intro j _
  exact bump_le_one (hu j)

/-- `J_r = (8/15)^r`, the total mass of `φ` on the unit cube (via Fubini). -/
def J (r : ℕ) : ℝ := (8 / 15) ^ r

lemma J_pos (r : ℕ) : 0 < J r := by
  unfold J
  positivity

lemma J_zero : J 0 = 1 := by
  unfold J
  norm_num

lemma J_one : J 1 = 8 / 15 := by
  unfold J
  norm_num

/-- Product of the one-dimensional masses equals `J_r`. -/
lemma prod_bump_integral (r : ℕ) :
    (∏ j : Fin r, ∫ x in (0:ℝ)..1, bump x) = J r := by
  have h : (∏ j : Fin r, ∫ x in (0:ℝ)..1, bump x)
      = (∫ x in (0:ℝ)..1, bump x) ^ (Fintype.card (Fin r)) :=
    Finset.prod_const _
  rw [h, bump_integral_eq, J, Fintype.card_fin]

/-! ## 3. Constants `a₀` and `c₀` -/

/-- `a₀ ≤ min{U-1, K/(8√r), 1}` of Proposition B.1. -/
def a0 (r : ℕ) (K U : ℝ) : ℝ := min (U - 1) (min (K / (8 * Real.sqrt r)) 1)

lemma a0_pos {r : ℕ} {K U : ℝ} (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    0 < a0 r K U := by
  unfold a0
  have h1 : 0 < U - 1 := by linarith
  have h2 : 0 < (r : ℝ) := by positivity
  have h3 : 0 < Real.sqrt r := Real.sqrt_pos.mpr h2
  have h4 : 0 < (8:ℝ) * Real.sqrt r := by positivity
  have h5 : 0 < K / (8 * Real.sqrt r) := div_pos hK h4
  exact lt_min h1 (lt_min h5 (by norm_num))

lemma a0_nonneg {r : ℕ} {K U : ℝ} (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    0 ≤ a0 r K U := (a0_pos hr hK hU).le

lemma a0_le_U_sub_one (r : ℕ) (K U : ℝ) : a0 r K U ≤ U - 1 := min_le_left _ _

lemma a0_le_one (r : ℕ) (K U : ℝ) : a0 r K U ≤ 1 :=
  le_trans (min_le_right _ _) (min_le_right _ _)

lemma a0_le_K_div (r : ℕ) (K U : ℝ) : a0 r K U ≤ K / (8 * Real.sqrt r) :=
  le_trans (min_le_right _ _) (min_le_left _ _)

/-- Lower-bound constant `c₀ = a₀ J_r / 6` of Proposition B.1. -/
def c0 (r : ℕ) (K U : ℝ) : ℝ := a0 r K U * J r / 6

lemma c0_eq (r : ℕ) (K U : ℝ) : c0 r K U = a0 r K U * J r / 6 := rfl

lemma c0_pos {r : ℕ} {K U : ℝ} (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    0 < c0 r K U := by
  unfold c0
  exact div_pos (mul_pos (a0_pos hr hK hU) (J_pos r)) (by norm_num)

lemma c0_nonneg {r : ℕ} {K U : ℝ} (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U) :
    0 ≤ c0 r K U := (c0_pos hr hK hU).le

/-- `a₀ J_r = 6 c₀`. -/
lemma a0_mul_J_eq (r : ℕ) (K U : ℝ) : a0 r K U * J r = 6 * c0 r K U := by
  unfold c0
  ring

/-! ## 4. Grid counting and cell mass -/

/-- If at most `N` of `L^r` cells are marked and `2N ≤ L^r`, then at least
`L^r / 2` cells remain unmarked (as reals). -/
lemma unmarked_cells_ge_half (L N r : ℕ) (hcount : 2 * N ≤ L ^ r) :
    ((L ^ r - N : ℕ) : ℝ) ≥ ((L ^ r : ℕ) : ℝ) / 2 := by
  have hNle : N ≤ L ^ r := by omega
  have hcast : ((L ^ r - N : ℕ) : ℝ) = ((L ^ r : ℕ) : ℝ) - (N : ℝ) :=
    Nat.cast_sub hNle
  have hNbound : (N : ℝ) ≤ ((L ^ r : ℕ) : ℝ) / 2 := by
    have h2 : (2 * N : ℕ) ≤ L ^ r := hcount
    have h2' : ((2 * N : ℕ) : ℝ) ≤ ((L ^ r : ℕ) : ℝ) := Nat.cast_le.mpr h2
    have h2'' : ((2 * N : ℕ) : ℝ) = 2 * (N : ℝ) := by norm_cast
    rw [h2''] at h2'
    nlinarith
  rw [hcast]
  nlinarith

/-- Mass of a single scaled bump on a cell of side `1/L`:
`a₀ J_r L^{-(r+1)}` (the paper's `a₀ J_r L^{-(r+1)}`). -/
def cellMass (a₀ Jr : ℝ) (L r : ℕ) : ℝ := a₀ * Jr / (L : ℝ) ^ (r + 1)

lemma cellMass_nonneg {a₀ Jr : ℝ} {L r : ℕ} (ha₀ : 0 ≤ a₀) (hJ : 0 ≤ Jr) :
    0 ≤ cellMass a₀ Jr L r := by
  unfold cellMass
  positivity

/-- Total mass when at least half the cells remain unmarked. -/
lemma mass_from_unmarked (a₀ Jr : ℝ) (L N r : ℕ) (ha₀ : 0 ≤ a₀) (hJ : 0 ≤ Jr)
    (hL : 0 < L) (hcount : 2 * N ≤ L ^ r) :
    ((L ^ r - N : ℕ) : ℝ) * cellMass a₀ Jr L r ≥ a₀ * Jr / (2 * L) := by
  have hhalf := unmarked_cells_ge_half L N r hcount
  have hmass := mul_le_mul_of_nonneg_right hhalf (cellMass_nonneg (L := L) (r := r) ha₀ hJ)
  have hL0 : (L : ℝ) ≠ 0 := by positivity
  have heq : ((L ^ r : ℕ) : ℝ) / 2 * cellMass a₀ Jr L r = a₀ * Jr / (2 * L) := by
    simp only [cellMass, Nat.cast_pow, pow_succ]
    field_simp
  rwa [heq] at hmass

/-! ## 5. Arithmetic of `L = ⌈(2N)^{1/r}⌉` -/

lemma one_div_le_one (r : ℕ) (hr : 1 ≤ r) : (1:ℝ) / r ≤ 1 := by
  have : (1:ℝ) ≤ r := by exact_mod_cast hr
  have : 0 < (r : ℝ) := by positivity
  rw [div_le_iff₀ this]
  nlinarith

/-- `(2N)^{1/r} ≤ 2 · N^{1/r}` for `N ≥ 0`, `r ≥ 1`. -/
lemma two_mul_rpow_le (N r : ℕ) (hr : 1 ≤ r) :
    (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r)) ≤ 2 * (((N : ℝ) ^ ((1:ℝ) / r))) := by
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg _
  have h2 : 0 ≤ (2:ℝ) := by norm_num
  have hcast : (((2 * N : ℕ) : ℝ)) = (2:ℝ) * N := by norm_cast
  rw [hcast, Real.mul_rpow h2 hN]
  have h2pow : (2:ℝ) ^ ((1:ℝ) / r) ≤ 2 := by
    have hle : (2:ℝ) ^ ((1:ℝ) / r) ≤ (2:ℝ) ^ (1:ℝ) := by
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (one_div_le_one r hr)
    rwa [Real.rpow_one] at hle
  exact mul_le_mul_of_nonneg_right h2pow (Real.rpow_nonneg hN _)

/-- Grid size bound: `L = ⌈(2N)^{1/r}⌉ ≤ 3 N^{1/r}` for `N ≥ 1`, `r ≥ 1`. -/
lemma ceil_two_rpow_le (N r : ℕ) (hN : 1 ≤ N) (hr : 1 ≤ r) :
    ((⌈(((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))⌉₊ : ℝ)) ≤ 3 * (((N : ℝ) ^ ((1:ℝ) / r))) := by
  have hx : 0 ≤ (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r)) := by positivity
  have h1 := Nat.ceil_lt_add_one hx
  have h2 := two_mul_rpow_le N r hr
  have h3 : (1:ℝ) ≤ ((N : ℝ) ^ ((1:ℝ) / r)) := by
    have h : 0 ≤ (1:ℝ) / r := by
      have : (0:ℝ) < r := by positivity
      positivity
    have hle : ((1:ℝ) ^ ((1:ℝ) / r)) ≤ ((N : ℝ) ^ ((1:ℝ) / r)) := by
      refine Real.rpow_le_rpow (by norm_num) ?_ h
      exact_mod_cast hN
    rwa [Real.one_rpow] at hle
  have h4 : (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r)) + 1
      ≤ 2 * (((N : ℝ) ^ ((1:ℝ) / r))) + 1 := by linarith
  have h5 : 2 * (((N : ℝ) ^ ((1:ℝ) / r))) + 1
      ≤ 3 * (((N : ℝ) ^ ((1:ℝ) / r))) := by nlinarith [h3]
  have h6 : ((⌈(((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))⌉₊ : ℝ))
      ≤ (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r)) + 1 := le_of_lt h1
  linarith

/-- `L^r ≥ 2N` when `L = ⌈(2N)^{1/r}⌉`, `r ≥ 1`. -/
lemma ceil_rpow_pow_ge (N r : ℕ) (hr : 1 ≤ r) :
    ((2 * N : ℕ) : ℝ) ≤ ((⌈(((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))⌉₊ : ℝ)) ^ r := by
  have hx : 0 ≤ (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r)) := by positivity
  have hceil : (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))
      ≤ ((⌈(((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))⌉₊ : ℝ)) := Nat.le_ceil _
  have h1r : ((1:ℝ) / r) * (r : ℝ) = 1 := by
    have : (0:ℝ) < r := by positivity
    field_simp
  have hbase : 0 ≤ ((2 * N : ℕ) : ℝ) := by positivity
  have hpow : (↑(2 * N) ^ ((1:ℝ) / r)) ^ (r : ℝ) = (↑(2 * N) : ℝ) := by
    rw [← Real.rpow_mul hbase, h1r, Real.rpow_one]
  have hge := Real.rpow_le_rpow hx hceil (by positivity : 0 ≤ (r : ℝ))
  rw [hpow, Real.rpow_natCast] at hge
  exact hge

/-! ## 6. Mass lower bound `μ ≥ c₀ (N+1)^{-1/r}` (B.2) -/

lemma rpow_neg_inv (x : ℝ) (hx : 0 < x) (r : ℕ) :
    x ^ (negInvR r) = (x ^ ((1:ℝ) / r))⁻¹ := by
  unfold negInvR
  rw [Real.rpow_neg (le_of_lt hx)]

/-- Core of (B.2) for `N ≥ 1`: `a₀ J_r / (2 L) ≥ c₀ N^{-1/r}` when
`L ≥ (2N)^{1/r}` and `L ≤ 3 N^{1/r}`. -/
lemma mu_bound_core {r N : ℕ} {a₀ Jr L : ℝ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (ha₀ : 0 < a₀) (hJ : 0 < Jr)
    (hL : (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r)) ≤ L)
    (hL_le : L ≤ 3 * (((N : ℝ) ^ ((1:ℝ) / r)))) :
    a₀ * Jr / (2 * L) ≥ (a₀ * Jr / 6) * (((N : ℝ) ^ (negInvR r))) := by
  have hN0 : 0 < (N : ℝ) := by positivity
  have hL0 : 0 < L :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos (by positivity) _) hL
  have hNr : 0 < ((N : ℝ) ^ ((1:ℝ) / r)) := Real.rpow_pos_of_pos hN0 _
  have hpow : (((N : ℝ) ^ (negInvR r))) = (((N : ℝ) ^ ((1:ℝ) / r)))⁻¹ :=
    rpow_neg_inv (N : ℝ) hN0 r
  have hkey : (a₀ * Jr / 6) * (((N : ℝ) ^ (negInvR r)))
      = a₀ * Jr / (6 * ((N : ℝ) ^ ((1:ℝ) / r))) := by
    rw [hpow]
    field_simp
  rw [hkey]
  have hcmp : 2 * L ≤ 6 * ((N : ℝ) ^ ((1:ℝ) / r)) := by nlinarith
  have hnum : 0 ≤ a₀ * Jr := mul_nonneg ha₀.le hJ.le
  exact div_le_div_of_nonneg_left hnum (by positivity) hcmp

/-- (B.2) for `N ≥ 1`. -/
lemma mu_ge_c0_of_pos {r N : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hN : 1 ≤ N) (hK : 0 < K) (hU : 1 < U)
    (μ : ℝ) (hμ : μ ≥ (a0 r K U * J r) / (2 *
      ((⌈(((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))⌉₊ : ℝ)))) :
    μ ≥ c0 r K U * (((N : ℝ) ^ (negInvR r))) := by
  have ha₀ : 0 < a0 r K U := a0_pos hr hK hU
  have hJ : 0 < J r := J_pos r
  set L : ℝ := ((⌈(((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))⌉₊ : ℝ)) with _hLdef
  have hL1 : (((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r)) ≤ L := Nat.le_ceil _
  have hL2 : L ≤ 3 * (((N : ℝ) ^ ((1:ℝ) / r))) := ceil_two_rpow_le N r hN hr
  have hcore := mu_bound_core hr hN ha₀ hJ hL1 hL2
  have hc0 : c0 r K U = a0 r K U * J r / 6 := rfl
  exact hcore.trans hμ

/-- (B.2) for `N = 0`: a full bump has mass `a₀ J_r = 6 c₀ ≥ c₀`. -/
lemma mu_ge_c0_of_zero {r : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U)
    (μ : ℝ) (hμ : μ ≥ a0 r K U * J r) :
    μ ≥ c0 r K U * (((0:ℝ) + 1) ^ (negInvR r)) := by
  have hc0 : c0 r K U = a0 r K U * J r / 6 := rfl
  have hone : (((0:ℝ) + 1) ^ (negInvR r)) = 1 := by
    rw [zero_add, Real.one_rpow]
  rw [hone, mul_one, hc0]
  have hpos := a0_pos hr hK hU
  have hJ := J_pos r
  nlinarith

/-- Uniform form of (B.2): `μ_e ≥ c₀ (N_e+1)^{-1/r}` for every query count. -/
lemma mu_ge_c0 {r N : ℕ} {K U : ℝ}
    (hr : 1 ≤ r) (hK : 0 < K) (hU : 1 < U)
    (μ : ℝ) (hN0 : N = 0 → μ ≥ a0 r K U * J r)
    (hNpos : 1 ≤ N → μ ≥ (a0 r K U * J r) / (2 *
      ((⌈(((2 * N : ℕ) : ℝ) ^ ((1:ℝ) / r))⌉₊ : ℝ)))) :
    μ ≥ c0 r K U * ((((N : ℝ) + 1) ^ (negInvR r))) := by
  rcases Nat.eq_zero_or_pos N with h | h
  · subst N
    simpa using mu_ge_c0_of_zero hr hK hU μ (hN0 rfl)
  · have hcore := mu_ge_c0_of_pos hr h hK hU μ (hNpos h)
    have hN0 : 0 < (N : ℝ) := by positivity
    have hpow_mono : ((N : ℝ) + 1) ^ negInvR r ≤ (N : ℝ) ^ negInvR r :=
      Real.rpow_le_rpow_of_exponent_nonpos hN0 (by linarith) (negInvR_nonpos r)
    exact (mul_le_mul_of_nonneg_left hpow_mono (c0_pos hr hK hU).le).trans hcore

/-! ## 7. Jensen / power-mean step -/

/-- `x ↦ x⁻¹` is convex on `(0,∞)`. -/
lemma convexOn_inv_Ioi : ConvexOn ℝ (Set.Ioi (0:ℝ)) (fun x => x⁻¹) := by
  simpa only [zpow_neg_one] using (convexOn_zpow (-1 : ℤ) :
    ConvexOn ℝ (Set.Ioi (0:ℝ)) (fun x : ℝ => x ^ (-1 : ℤ)))

/-- `x ↦ x^{1/r}` is concave on `Ioi 0` for `r ≥ 1`. -/
lemma concaveOn_rpow_one_div (r : ℕ) (hr : 1 ≤ r) :
    ConcaveOn ℝ (Set.Ioi (0:ℝ)) (fun x : ℝ => x ^ ((1:ℝ) / r)) := by
  have h1 : (0:ℝ) ≤ (1:ℝ) / r := by
    have : (0:ℝ) < r := by positivity
    positivity
  have h2 : (1:ℝ) / r ≤ 1 := one_div_le_one r hr
  exact (Real.concaveOn_rpow h1 h2).subset Set.Ioi_subset_Ici_self (convex_Ioi _)

/-- `x ↦ x^{-1/r}` is convex on `(0,∞)` for `r ≥ 1`. -/
lemma convexOn_rpow_neg_one_div (r : ℕ) (hr : 1 ≤ r) :
    ConvexOn ℝ (Set.Ioi (0:ℝ)) (fun x : ℝ => x ^ (negInvR r)) := by
  have hf := concaveOn_rpow_one_div r hr
  have himage : (fun x : ℝ => x ^ ((1:ℝ) / r)) '' Set.Ioi (0:ℝ) ⊆ Set.Ioi (0:ℝ) := by
    rintro _ ⟨x, hx, rfl⟩
    exact Real.rpow_pos_of_pos hx _
  have hconvImage : Convex ℝ ((fun x : ℝ => x ^ ((1:ℝ) / r)) '' Set.Ioi (0:ℝ)) := by
    have hsurj : (fun x : ℝ => x ^ ((1:ℝ) / r)) '' Set.Ioi (0:ℝ) = Set.Ioi (0:ℝ) := by
      apply Set.Subset.antisymm himage
      intro y hy
      refine ⟨y ^ (r : ℝ), Real.rpow_pos_of_pos hy _, ?_⟩
      change (y ^ (r : ℝ)) ^ ((1:ℝ) / r) = y
      rw [← Real.rpow_mul hy.le]
      have : (r : ℝ) * ((1:ℝ) / r) = 1 := by
        field_simp
      rw [this, Real.rpow_one]
    rw [hsurj]
    exact convex_Ioi _
  have hg := convexOn_inv_Ioi.subset himage hconvImage
  have hanti : AntitoneOn (fun x : ℝ => x⁻¹)
      ((fun x : ℝ => x ^ ((1:ℝ) / r)) '' Set.Ioi (0:ℝ)) := by
    intro u hu v hv huv
    exact (inv_le_inv₀ (himage hv) (himage hu)).mpr huv
  have hcomp := hg.comp_concaveOn hf hanti
  refine hcomp.congr ?_
  intro x hx
  simp only [Function.comp_apply, negInvR, Real.rpow_neg hx.le]

/-- Jensen step of (B.1):
`∑_e (N_e+1)^{-1/r} ≥ m^{1+1/r} (N_qry+m)^{-1/r}`
for `N_qry = ∑_e N_e`. -/
lemma jensen_pow_neg {m r : ℕ} (hm : 1 ≤ m) (hr : 1 ≤ r)
    (N : Fin m → ℕ) :
    (∑ e : Fin m, (((N e : ℝ) + 1) ^ negInvR r)) ≥
      (m : ℝ) ^ ((1:ℝ) + 1 / r) *
        ((∑ e : Fin m, (N e : ℝ)) + m) ^ negInvR r := by
  have hm0 : 0 < (m : ℝ) := by positivity
  have hms : 0 < (∑ e : Fin m, (N e : ℝ)) + m := by positivity
  have hw1 : (∑ _e : Fin m, (m : ℝ)⁻¹) = 1 := by
    simp [hm0.ne']
  have hj := (convexOn_rpow_neg_one_div r hr).map_sum_le
    (p := fun e : Fin m => (N e : ℝ) + 1)
    (w := fun _ : Fin m => (m : ℝ)⁻¹) (t := Finset.univ)
    (fun _ _ => inv_nonneg.mpr hm0.le) hw1 (fun e _ => show 0 < (N e : ℝ) + 1 from by positivity)
  simp only [Algebra.id.smul_eq_mul] at hj
  have hs : (∑ e : Fin m, ((N e : ℝ) + 1)) = (∑ e : Fin m, (N e : ℝ)) + m := by
    simp [Finset.sum_add_distrib]
  simp only [← Finset.mul_sum] at hj
  rw [hs] at hj
  rw [Real.mul_rpow (inv_nonneg.mpr hm0.le) hms.le,
    Real.inv_rpow hm0.le, negInvR, Real.rpow_neg hm0.le, inv_inv] at hj
  have hmul := mul_le_mul_of_nonneg_left hj hm0.le
  simp only [← mul_assoc, mul_inv_cancel₀ hm0.ne', one_mul] at hmul
  rw [← Real.rpow_one_add' hm0.le (by positivity)] at hmul
  exact hmul

/-! ## 8. Logarithmic accuracy step -/

/-- `log(1+x) ≥ x/(1+x)` for `x > -1`. -/
lemma log_one_add_ge_div (x : ℝ) (hx : 0 < 1 + x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have h := Real.one_sub_inv_le_log_of_pos hx
  have h2 : (1:ℝ) - (1 + x)⁻¹ = x / (1 + x) := by
    field_simp
    ring
  rw [← h2]
  exact h

/-- `log(1+x) ≥ x/U` whenever `0 ≤ x ≤ U-1` and `U ≥ 1`. -/
lemma log_one_add_ge_div_U {x U : ℝ} (hx : 0 ≤ x) (hU : 1 ≤ U) (hxU : x ≤ U - 1) :
    x / U ≤ Real.log (1 + x) := by
  have h1 : 0 < 1 + x := by linarith
  have hdiv := log_one_add_ge_div x h1
  have hle : x / (1 + x) ≥ x / U := by
    have hU0 : 0 < U := by linarith
    have hden : (1 + x) ≤ U := by linarith
    rcases eq_or_lt_of_le hx with hx0 | hx0
    · subst hx0
      norm_num
    · exact div_le_div_of_nonneg_left hx0.le (by positivity) hden
  linarith

/-- Product log error: if each factor has log-error at most `δ`, the product
has log-error at most `m δ`. -/
lemma log_prod_error {m : ℕ} (f g : Fin m → ℝ)
    (hf : ∀ e, 1 ≤ f e) (hg : ∀ e, 1 ≤ g e)
    (herr : ∀ e, |Real.log (g e) - Real.log (f e)| ≤ (δ : ℝ)) :
    |Real.log (∏ e, g e) - Real.log (∏ e, f e)| ≤ (m : ℝ) * δ := by
  have hF : Real.log (∏ e, f e) = ∑ e, Real.log (f e) := by
    refine Real.log_prod Finset.univ f ?_
    intro e _
    exact (lt_of_lt_of_le (by norm_num) (hf e)).ne'
  have hG : Real.log (∏ e, g e) = ∑ e, Real.log (g e) := by
    refine Real.log_prod Finset.univ g ?_
    intro e _
    exact (lt_of_lt_of_le (by norm_num) (hg e)).ne'
  rw [hF, hG]
  have hsum : |∑ e, Real.log (g e) - ∑ e, Real.log (f e)|
      = |∑ e, (Real.log (g e) - Real.log (f e))| := by
    rw [Finset.sum_sub_distrib]
  rw [hsum]
  have habs : |∑ e, (Real.log (g e) - Real.log (f e))|
      ≤ ∑ e, |Real.log (g e) - Real.log (f e)| :=
    Finset.abs_sum_le_sum_abs _ _
  have hconst : (∑ e : Fin m, δ) = (m : ℝ) * δ := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hle : (∑ e : Fin m, |Real.log (g e) - Real.log (f e)|) ≤ (m : ℝ) * δ := by
    rw [← hconst]
    exact Finset.sum_le_sum fun e _ => herr e
  exact le_trans habs hle

/-- Converse surrogate step: when both factors are `≥ 1`, the log-difference
is bounded by the absolute difference. -/
lemma surrogate_log_le_abs {Ψ Ψs : ℝ} (hΨ : 1 ≤ Ψ) (hΨs : 1 ≤ Ψs) :
    |Real.log Ψs - Real.log Ψ| ≤ |Ψs - Ψ| :=
  log_abs_sub_le_abs_sub hΨs hΨ

/-- If each surrogate is within `ε/M` and both are `≥ 1`, the product
partition functions differ by a factor in `[e^{-ε}, e^{ε}]`. -/
lemma surrogate_product_factor {m : ℕ} (f g : Fin m → ℝ) {ε : ℝ}
    (hf : ∀ e, 1 ≤ f e) (hg : ∀ e, 1 ≤ g e)
    (herr : ∀ e, |g e - f e| ≤ ε / (m : ℝ)) (hm : 0 < m) (hε : 0 ≤ ε) :
    Real.exp (-ε) ≤ (∏ e, g e) / (∏ e, f e) ∧
      (∏ e, g e) / (∏ e, f e) ≤ Real.exp ε := by
  have herr' : ∀ e, |Real.log (g e) - Real.log (f e)| ≤ ε / (m : ℝ) := by
    intro e
    exact (surrogate_log_le_abs (hf e) (hg e)).trans (herr e)
  have h := log_prod_error f g hf hg herr'
  have hεm : (m : ℝ) * (ε / (m : ℝ)) = ε := by
    field_simp
  have hlog : |Real.log (∏ e, g e) - Real.log (∏ e, f e)| ≤ ε := by
    rw [← hεm]
    exact h
  have hpF : 0 < ∏ e, f e :=
    Finset.prod_pos fun e _ => lt_of_lt_of_le (by norm_num) (hf e)
  have hpG : 0 < ∏ e, g e :=
    Finset.prod_pos fun e _ => lt_of_lt_of_le (by norm_num) (hg e)
  have hdiv : Real.log ((∏ e, g e) / (∏ e, f e))
      = Real.log (∏ e, g e) - Real.log (∏ e, f e) :=
    Real.log_div hpG.ne' hpF.ne'
  have habs : |Real.log ((∏ e, g e) / (∏ e, f e))| ≤ ε := by
    rw [hdiv]
    exact hlog
  have h1 : Real.log ((∏ e, g e) / (∏ e, f e)) ≤ ε := le_trans (le_abs_self _) habs
  have h2 : -Real.log ((∏ e, g e) / (∏ e, f e)) ≤ ε :=
    le_trans (neg_le_abs _) habs
  have h3 : Real.exp (-ε) ≤ (∏ e, g e) / (∏ e, f e) := by
    rw [← Real.exp_log (div_pos hpG hpF), Real.exp_le_exp]
    linarith
  have h4 : (∏ e, g e) / (∏ e, f e) ≤ Real.exp ε := by
    rw [← Real.exp_log (div_pos hpG hpF), Real.exp_le_exp]
    exact h1
  exact ⟨h3, h4⟩

/-! ## 9. Combination: the query lower bound (B.1) -/

/-- Algebraic content of (B.1).  From the accuracy-forced inequality
`(c₀/U) m^{1+1/r} (N_qry+m)^{-1/r} ≤ 2ε` one deduces
`N_qry ≥ (c₀/(2Uε))^r m^{r+1} - m`. -/
theorem query_lower_bound {r m N_qry : ℕ} {K U ε : ℝ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hK : 0 < K) (hU : 1 < U)
    (hε0 : 0 < ε) (_hε1 : ε ≤ 1)
    (h : (c0 r K U / U) * (m : ℝ) ^ ((1:ℝ) + 1 / r) *
        ((N_qry : ℝ) + m) ^ negInvR r ≤ 2 * ε) :
    (N_qry : ℝ) ≥ (c0 r K U / (2 * U * ε)) ^ r * (m : ℝ) ^ (r + 1) - m := by
  have hc : 0 < c0 r K U := c0_pos hr hK hU
  have hm0 : 0 < (m : ℝ) := by positivity
  have hU0 : 0 < U := by linarith
  have hr0 : 0 < (r : ℝ) := by positivity
  have hN : 0 < (N_qry : ℝ) + m := by positivity
  have hmp : 0 < (m : ℝ) ^ ((1:ℝ) + 1 / r) := Real.rpow_pos_of_pos hm0 _
  have hs : 0 < ((N_qry : ℝ) + m) ^ ((1:ℝ) / r) := Real.rpow_pos_of_pos hN _
  rw [rpow_neg_inv _ hN] at h
  have ha : c0 r K U / (2 * U * ε) * (m : ℝ) ^ ((1:ℝ) + 1 / r) ≤
      ((N_qry : ℝ) + m) ^ ((1:ℝ) / r) := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity : 0 < 2 * U * ε)).mpr
    have hm := (mul_inv_le_iff₀ hs).mp h
    have hmU := (div_le_iff₀ hU0).mp (show c0 r K U *
        (m : ℝ) ^ ((1:ℝ) + 1 / r) / U ≤
        2 * ε * ((N_qry : ℝ) + m) ^ ((1:ℝ) / r) by
      simpa only [div_mul_eq_mul_div] using hm)
    convert hmU using 1 <;> field_simp <;> ring
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ c0 r K U / (2 * U * ε) *
    (m : ℝ) ^ ((1:ℝ) + 1 / r)) ha r
  have hid : (((N_qry : ℝ) + m) ^ ((1:ℝ) / r)) ^ r = (N_qry : ℝ) + m := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    have : ((1:ℝ) / r) * (r : ℝ) = 1 := by field_simp
    rw [this, Real.rpow_one]
  have hidm : ((m : ℝ) ^ ((1:ℝ) + 1 / r)) ^ r = (m : ℝ) ^ (r + 1) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hm0.le]
    have : ((1:ℝ) + 1 / r) * (r : ℝ) = (r + 1 : ℕ) := by
      push_cast
      field_simp
    rw [this, Real.rpow_natCast]
  rw [mul_pow, hidm, hid] at hp
  linarith

/-- Proposition B.1, analytic form (B.1): under the accuracy constraint
`log Z₁ ≤ 2ε` forced by the fooling-function construction and Jensen, every
deterministic value-query algorithm uses at least
`(c₀/(2Uε))^r m^{r+1} - m` queries in the worst case. -/
theorem prop_B1 {r m N_qry : ℕ} {K U ε : ℝ}
    (hr : 1 ≤ r) (hm : 1 ≤ m) (hK : 0 < K) (hU : 1 < U)
    (hε0 : 0 < ε) (hε1 : ε ≤ 1)
    (N : Fin m → ℕ)
    (hsum : (∑ e, (N e : ℝ)) = (N_qry : ℝ))
    (hlogZ : (c0 r K U / U) * (∑ e, (((N e : ℝ) + 1) ^ (negInvR r))) ≤ 2 * ε) :
    (N_qry : ℝ) ≥ (c0 r K U / (2 * U * ε)) ^ r * ((m : ℝ) ^ (r + 1)) - m := by
  have hj := jensen_pow_neg hm hr N
  have hc0 : 0 < c0 r K U := c0_pos hr hK hU
  have hU0 : 0 < U := by linarith
  have hpos : 0 ≤ (c0 r K U / U) := (div_pos hc0 hU0).le
  have hle : (c0 r K U / U) * ((m : ℝ) ^ ((1:ℝ) + 1 / r) *
      ((((∑ e : Fin m, (N e : ℝ)) + m) ^ (negInvR r))))
      ≤ (c0 r K U / U) * (∑ e, (((N e : ℝ) + 1) ^ (negInvR r))) :=
    mul_le_mul_of_nonneg_left hj hpos
  have hsum2 : (∑ e : Fin m, (N e : ℝ)) + m = (N_qry : ℝ) + m := by
    rw [hsum]
  rw [hsum2] at hle
  have hchain : (c0 r K U / U) * ((m : ℝ) ^ ((1:ℝ) + 1 / r)) *
      ((((N_qry : ℝ) + m) ^ (negInvR r))) ≤ 2 * ε :=
    by simpa only [mul_assoc] using le_trans hle hlogZ
  exact query_lower_bound hr hm hK hU hε0 hε1 hchain

/-! ## 10. Converse upper bound: mesh and sample budget -/

/-- Dyadic mesh choice `a ≤ ε/(2 K √r M)` is positive. -/
lemma mesh_size_pos {ε K r M : ℝ} (hε : 0 < ε) (hK : 0 < K)
    (hr : 0 < r) (hM : 0 < M) :
    0 < ε / (2 * K * Real.sqrt r * M) := by
  positivity

/-- Surrogate range step: projecting an approximate value onto `[1,∞)` does
not increase the error from a true factor value `≥ 1`. -/
lemma project_one_le_abs {y Ψ : ℝ} (hΨ : 1 ≤ Ψ) :
    |max 1 y - Ψ| ≤ |y - Ψ| := by
  rcases le_total y 1 with hy | hy
  · rw [max_eq_left hy]
    rcases le_total y Ψ with h | h
    · rw [abs_of_nonpos (by linarith : (1:ℝ) - Ψ ≤ 0),
        abs_of_nonpos (by linarith : y - Ψ ≤ 0)]
      linarith
    · rw [abs_of_nonneg (by linarith : (1:ℝ) - Ψ ≥ 0),
        abs_of_nonneg (by linarith : y - Ψ ≥ 0)]
      linarith
  · rw [max_eq_right hy]

/-- Sample-error budget of the converse: two halves of `ε/M` sum to `ε/M`. -/
lemma surrogate_total_error {ε M : ℝ} (hε : 0 < ε) (hM : 0 < M) :
    ε / (2 * M) + ε / (2 * M) ≤ ε / M := by
  have h : ε / (2 * M) + ε / (2 * M) = ε / M := by
    field_simp
    ring
  linarith

end LowerBound
end Paper08
