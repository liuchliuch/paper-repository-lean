import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Paper08.Basic
import Paper08.Quadrature
import Paper08.Coeff
import Paper08.Moments
import Paper08.Algorithm

/-!
# Theorem 1.2 — deterministic FPTAS (algebraic content)

The three-term accuracy split, the regime inequality (1.3)
`3c√(r-1) q ≤ 1-σ`, and the `e^{±ε}` form of the accuracy guarantee.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace FPTAS

open Coeff Moments Quadrature

/-- `log(1+x) < x` for `x > 0`. -/
lemma log_one_add_lt_self {x : ℝ} (hx : 0 < x) : Real.log (1 + x) < x := by
  rw [Real.log_lt_iff_lt_exp (by linarith : 0 < 1 + x)]
  have := Real.add_one_lt_exp (ne_of_gt hx)
  linarith

lemma sqrt_two_lt_three_halves : Real.sqrt 2 < 3 / 2 := by
  rw [Real.sqrt_lt (by norm_num) (by norm_num)]
  norm_num

/-- Structural hypothesis of Theorem 1.2. -/
structure Params where
  r : ℕ
  c : ℕ
  K : ℝ
  q : ℝ
  σ : ℝ
  r_ge : 2 ≤ r
  c_ge : 1 ≤ c
  K_pos : 0 < K
  q_pos : 0 < q
  σ_range : 0 < σ ∧ σ < 1
  regime : 3 * c * Real.sqrt (r - 1) * q ≤ 1 - σ

lemma sqrt_r_sub_one_pos (p : Params) : 0 < Real.sqrt (p.r - 1) := by
  apply Real.sqrt_pos.mpr
  have h : (2:ℝ) ≤ p.r := by exact_mod_cast p.r_ge
  linarith

/-- `β = 1 / (3 c √(r-1) q)` of Lemma 2.1. -/
def beta (p : Params) : ℝ := 1 / (3 * p.c * Real.sqrt (p.r - 1) * p.q)

lemma beta_pos (p : Params) : 0 < beta p := by
  unfold beta
  apply div_pos
  · norm_num
  · have hc : (0:ℝ) < p.c := by
      have h := p.c_ge
      exact_mod_cast (by omega : 0 < p.c)
    have hq : 0 < p.q := p.q_pos
    have hs : 0 < Real.sqrt (p.r - 1) := sqrt_r_sub_one_pos p
    have ha : 0 < (3:ℝ) * p.c := by nlinarith
    have hb : 0 < Real.sqrt (p.r - 1) * p.q := by nlinarith
    nlinarith [mul_pos ha hb]

/-- From (1.3): `β ≥ 1/(1-σ)`. -/
lemma beta_ge_inv_one_sub_sigma (p : Params) :
    1 / (1 - p.σ) ≤ beta p := by
  unfold beta
  have hc : (0:ℝ) < p.c := by
    have h := p.c_ge
    exact_mod_cast (by omega : 0 < p.c)
  have hq : 0 < p.q := p.q_pos
  have hs : 0 < Real.sqrt (p.r - 1) := sqrt_r_sub_one_pos p
  have ha : 0 < (3:ℝ) * p.c := by nlinarith
  have hb : 0 < Real.sqrt (p.r - 1) * p.q := by nlinarith
  have hpos : 0 < 3 * p.c * Real.sqrt (p.r - 1) * p.q := by nlinarith [mul_pos ha hb]
  have hreg : 3 * p.c * Real.sqrt (p.r - 1) * p.q ≤ 1 - p.σ := p.regime
  have hσ : 0 < 1 - p.σ := by linarith [p.σ_range.2]
  rw [div_le_div_iff₀ hσ hpos]
  nlinarith

lemma beta_gt_one (p : Params) : 1 < beta p := by
  have h := beta_ge_inv_one_sub_sigma p
  have hσ : 0 < 1 - p.σ := by linarith [p.σ_range.2]
  have hinv : 1 < 1 / (1 - p.σ) := by
    rw [lt_div_iff₀ hσ]
    nlinarith [p.σ_range.1]
  linarith

/-- The weak-interaction regime puts every log-factor in `[0,1/3)`. -/
theorem q_lt_third (p : Params) : p.q < 1 / 3 := by
  have hr : (2 : ℝ) ≤ p.r := by exact_mod_cast p.r_ge
  have hc : (1 : ℝ) ≤ p.c := by exact_mod_cast p.c_ge
  have hs : (1 : ℝ) ≤ Real.sqrt (p.r - 1) := by
    have h := Real.sqrt_le_sqrt (show (1 : ℝ) ≤ p.r - 1 by linarith)
    simpa only [Real.sqrt_one] using h
  have hprod : 1 ≤ (p.c : ℝ) * Real.sqrt (p.r - 1) := by nlinarith
  have hq := mul_le_mul_of_nonneg_right hprod p.q_pos.le
  have hreg := p.regime
  nlinarith [p.σ_range.1]

/-- The projected oracle interval `[1,2]` contains the factor range. -/
theorem exp_q_lt_two (p : Params) : Real.exp p.q < 2 := by
  have h : p.q < Real.log 2 := by linarith [q_lt_third p, Real.log_two_gt_d9]
  have he := Real.exp_lt_exp.mpr h
  simpa only [Real.exp_log (by norm_num : (0 : ℝ) < 2)] using he

/-- Accuracy split (4.2): `τ_0 = ε / (3 s m (4 A₀ F)^s)`. -/
def primitiveTol (ε : ℝ) (s m A₀ F : ℕ) : ℝ :=
  ε / (3 * s * m * (4 * A₀ * F) ^ s)

lemma primitiveTol_pos {ε : ℝ} {s m A₀ F : ℕ}
    (hε : 0 < ε) (hs : 1 ≤ s) (hm : 1 ≤ m) (hA : 1 ≤ A₀) (hF : 1 ≤ F) :
    0 < primitiveTol ε s m A₀ F := by
  unfold primitiveTol
  apply div_pos hε
  have h1 : (0:ℝ) < s := by exact_mod_cast hs
  have h2 : (0:ℝ) < m := by exact_mod_cast hm
  have hA0 : (1:ℝ) ≤ A₀ := by exact_mod_cast hA
  have hF0 : (1:ℝ) ≤ F := by exact_mod_cast hF
  have hbase : (1:ℝ) ≤ (4:ℝ) * A₀ * F := by nlinarith [hA0, hF0]
  have hpow : 1 ≤ ((4:ℝ) * A₀ * F) ^ s := one_le_pow₀ hbase
  have ha : 0 < (3:ℝ) * s * m := by nlinarith
  have hb : 0 < ((4:ℝ) * A₀ * F) ^ s := by nlinarith
  nlinarith [mul_pos ha hb]

/-- Theorem 1.2 accuracy conclusion. -/
def Accurate (Zhat Z ε : ℝ) : Prop :=
  Z > 0 ∧ Zhat > 0 ∧ |Real.log Zhat - Real.log Z| ≤ ε

lemma accurate_exp_form {Zhat Z ε : ℝ}
    (h : Accurate Zhat Z ε) :
    Real.exp (-ε) ≤ Zhat / Z ∧ Zhat / Z ≤ Real.exp ε := by
  rcases h with ⟨hZ, hZhat, hlog⟩
  have hpos : 0 < Zhat / Z := by positivity
  have hlogdiv : Real.log (Zhat / Z) = Real.log Zhat - Real.log Z := by
    rw [Real.log_div (by linarith) (by linarith)]
  have hle := abs_le.mp hlog
  constructor
  · have h1 : Real.exp (-ε) ≤ Real.exp (Real.log (Zhat / Z)) := by
      apply Real.exp_le_exp.mpr
      rw [hlogdiv]
      linarith
    rwa [Real.exp_log hpos] at h1
  · have h2 : Real.log (Zhat / Z) ≤ ε := by rw [hlogdiv]; linarith
    rw [← Real.exp_log hpos]
    exact Real.exp_le_exp.mpr h2

/-- Corollary 1.3: the choice `σ = 1/11` is admissible. -/
lemma sigma_choice : (0:ℝ) < 1 / 11 ∧ (1 / 11 : ℝ) < 1 := by norm_num

/-- `log(3/2) < 5/12` used in the `η = 2` case of Corollary 1.3.
Proof: `exp(5/12) > 1 + 5/12 + (5/12)^2/2 + (5/12)^3/6 + (5/12)^4/24 > 3/2`. -/
lemma log_three_halves_lt : Real.log (3 / 2) < 5 / 12 := by
  have hpos : (0:ℝ) < 3 / 2 := by norm_num
  rw [Real.log_lt_iff_lt_exp hpos]
  have hx : (0:ℝ) ≤ 5 / 12 := by norm_num
  have hsum := Real.sum_le_exp_of_nonneg (x := 5 / 12) hx 5
  have hcalc : (3 / 2 : ℝ) < ∑ i ∈ Finset.range 5, (5 / 12 : ℝ) ^ i / Nat.factorial i := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
    norm_num
  linarith

/-- Range conversion for `η = 2` after (A.1):
`(11/10)·3Δ√η·q < 1` with `q = log(3/2)/(2Δ)`. -/
lemma eta_two_bound {Δ : ℝ} (hΔ : 1 ≤ Δ) :
    (11 / 10 : ℝ) * 3 * Δ * Real.sqrt 2 * (Real.log (3 / 2) / (2 * Δ)) < 1 := by
  have hlog := log_three_halves_lt
  have hs := sqrt_two_lt_three_halves
  have hlogpos : 0 ≤ Real.log (3 / 2) :=
    Real.log_nonneg (by norm_num : (1:ℝ) ≤ 3 / 2)
  have hpos : 0 < 2 * Δ := by nlinarith
  have hform : (11 / 10 : ℝ) * 3 * Δ * Real.sqrt 2 * (Real.log (3 / 2) / (2 * Δ))
      = (11 / 10) * (3 / 2) * Real.sqrt 2 * Real.log (3 / 2) := by
    field_simp
  rw [hform]
  have hprod : (11 / 10 : ℝ) * (3 / 2) * Real.sqrt 2 * Real.log (3 / 2)
      = (33 / 20) * Real.sqrt 2 * Real.log (3 / 2) := by ring
  rw [hprod]
  -- (33/20) √2 log(3/2) < (33/20) (3/2) (5/12) = (33/20)(15/24) = (33/20)(5/8) = 165/160
  -- but we need a sharper estimate: use √2 < 3/2 and log(3/2) < 5/12
  -- (33/20)*(3/2)*(5/12) = 33*3*5 / (20*2*12) = 495/480 = 33/32 > 1.  Still too crude.
  -- Use the paper's bound: (33/20)*√2*log(3/2) with log(3/2)<5/12
  -- = (33/20)*√2*(5/12) = (11/16)*√2 < 1  since 11√2 < 16 iff 242 < 256.
  have h11 : Real.log (3 / 2) < 5 / 12 := hlog
  have h2 : (33 / 20 : ℝ) * Real.sqrt 2 * Real.log (3 / 2)
      < (33 / 20) * Real.sqrt 2 * (5 / 12) := by
    nlinarith [Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)]
  have h3 : (33 / 20 : ℝ) * Real.sqrt 2 * (5 / 12) = (11 / 16) * Real.sqrt 2 := by ring
  have h4 : (11 / 16 : ℝ) * Real.sqrt 2 < 1 := by
    have hs : Real.sqrt 2 < 16 / 11 := by
      rw [Real.sqrt_lt (by norm_num) (by norm_num)]
      norm_num
    nlinarith [Real.sqrt_nonneg 2]
  nlinarith [h2, h3, h4]

/-- `log(1+x) < x` gives `log(1+1/η) < 1/η` for `η > 0`. -/
lemma log_one_add_inv_lt {η : ℝ} (hη : 0 < η) :
    Real.log (1 + 1 / η) < 1 / η :=
  log_one_add_lt_self (x := 1 / η) (by positivity)

end FPTAS
end Paper08
