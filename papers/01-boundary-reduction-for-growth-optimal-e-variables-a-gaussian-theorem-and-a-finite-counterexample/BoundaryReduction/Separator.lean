import BoundaryReduction.Appendix
import BoundaryReduction.Pinsker
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

open Real Set BigOperators
open scoped Classical
namespace BoundaryReduction.NinePoint

noncomputable def tiltProb (θ : ℝ × ℝ) : FinProb (Fin 9) :=
  ⟨pt θ, fun y => (pt_pos θ y).le, pt_sum θ⟩

/-- Axis mass minus diagonal mass. -/
def separator : Fin 9 → ℝ := fun y =>
  if y = 0 then 0 else if y.val ≤ 4 then 1 else -1

lemma separator_bounded (y : Fin 9) : |separator y| ≤ 1 := by
  fin_cases y <;> norm_num [separator]

lemma separator_base : FinProb.expect baseProb separator = 0 := by
  norm_num [FinProb.expect, baseProb, p0, separator, Fin.sum_univ_succ]

lemma cosh_quadratic_lower (x : ℝ) : 1 + x ^ 2 / 2 ≤ cosh x := by
  have h := (hasSum_cosh x).summable.sum_le_tsum (Finset.range 2)
    (fun n _ => div_nonneg (pow_nonneg (sq_nonneg x) n |>.trans_eq (pow_mul x 2 n).symm)
      (Nat.cast_nonneg _))
  norm_num [Finset.sum_range_succ] at h
  rwa [← cosh_eq_tsum] at h

/-- A rational quadratic upper envelope; the argument has square at most 0.0032. -/
lemma cosh_quadratic_upper {x : ℝ} (hx : x ^ 2 ≤ 2 / 625) :
    cosh x ≤ 1 + (501 / 1000 : ℝ) * x ^ 2 := by
  have hx0 : 0 ≤ x ^ 2 / 2 := by positivity
  have hx1 : x ^ 2 / 2 < 1 := by linarith
  refine (cosh_le_exp_half_sq x).trans
    ((exp_bound_div_one_sub_of_interval hx0 hx1).trans ?_)
  apply (div_le_iff₀ (by linarith : 0 < 1 - x ^ 2 / 2)).mpr
  have hprod := mul_nonneg (sq_nonneg x) (show 0 ≤ (2 / 625 : ℝ) - x ^ 2 by linarith)
  nlinarith

noncomputable def Z8 (u v : ℝ) := 2 * cosh u + 2 * cosh v + 4 * cosh (ρ*u) * cosh (ρ*v)
noncomputable def N (u v : ℝ) := 2 * cosh u + 2 * cosh v - 4 * cosh (ρ*u) * cosh (ρ*v)

lemma cosh_rho_upper {x : ℝ} (hx : x ^ 2 ≤ 1 / 100) :
    cosh (ρ*x) ≤ 1 + (501 / 1000 : ℝ) * (8 / 25) * x ^ 2 := by
  have heq : (ρ*x)^2 = (8 / 25 : ℝ) * x^2 := by rw [mul_pow, ρ_sq]
  have h := cosh_quadratic_upper (x := ρ*x) (by rw [heq]; nlinarith)
  rw [heq] at h
  simpa only [mul_assoc] using h

lemma N_lower {u v : ℝ} (hs : u ^ 2 + v ^ 2 ≤ 1 / 100) :
    (35 / 100 : ℝ) * (u ^ 2 + v ^ 2) ≤ N u v := by
  have hu := cosh_rho_upper (x := u) (by nlinarith [sq_nonneg v])
  have hv := cosh_rho_upper (x := v) (by nlinarith [sq_nonneg u])
  have hu0 : 0 ≤ cosh (ρ*u) := (cosh_pos _).le
  have hv0 : 0 ≤ 1 + (501 / 1000 : ℝ) * (8 / 25) * v^2 := by positivity
  have hmul := mul_le_mul hu hv ((cosh_pos _).le) (by positivity)
  have hquart : u^2*v^2 ≤ (u^2+v^2)^2 / 4 := by nlinarith [sq_nonneg (u^2-v^2)]
  have hss : (u^2+v^2)^2 ≤ (1/100 : ℝ)*(u^2+v^2) := by
    nlinarith [sq_nonneg u, sq_nonneg v]
  dsimp [N]
  nlinarith [cosh_quadratic_lower u, cosh_quadratic_lower v]

lemma cosh_small_upper {x : ℝ} (hx : x^2 ≤ 1/100) : cosh x ≤ 200/199 := by
  refine (cosh_le_exp_half_sq x).trans
    ((exp_bound_div_one_sub_of_interval (by positivity) (by linarith)).trans ?_)
  apply (div_le_iff₀ (by linarith : 0 < 1-x^2/2)).mpr
  linarith

lemma Z8_upper {u v : ℝ} (hs : u^2+v^2 ≤ 1/100) : Z8 u v < 9 := by
  have hu : u^2 ≤ 1/100 := by nlinarith [sq_nonneg v]
  have hv : v^2 ≤ 1/100 := by nlinarith [sq_nonneg u]
  have hcu := cosh_small_upper hu
  have hcv := cosh_small_upper hv
  have hd := mul_le_mul (cosh_rho_upper hu) (cosh_rho_upper hv)
    ((cosh_pos _).le) (by positivity)
  have hru : cosh (ρ*u) ≤ (501 : ℝ)/500 := by nlinarith [cosh_rho_upper hu]
  have hrv : cosh (ρ*v) ≤ (501 : ℝ)/500 := by nlinarith [cosh_rho_upper hv]
  have hprod := mul_le_mul hru hrv ((cosh_pos _).le) (by norm_num : (0:ℝ) ≤ 501/500)
  dsimp [Z8]
  nlinarith

lemma Z_eq_cosh (u v : ℝ) : Z (u,v) = ε + w * Z8 u v := by
  norm_num [Z, un, dot, coord, p0, Fin.sum_univ_succ, Fin.succ]
  simp only [Z8, cosh_eq, exp_add, exp_neg, neg_mul, mul_neg,
    mul_zero, zero_mul, zero_add, add_zero, mul_one, mul_neg_one, exp_zero]
  rw [mul_comm u ρ, mul_comm v ρ]
  ring

lemma separator_expect (u v : ℝ) :
    FinProb.expect (tiltProb (u,v)) separator = w * N u v / Z (u,v) := by
  norm_num [FinProb.expect, tiltProb, pt, un, dot, coord, p0, separator,
    Fin.sum_univ_succ, Fin.succ]
  simp only [N, cosh_eq, exp_add, exp_neg, neg_mul, mul_neg,
    mul_zero, zero_mul, zero_add, add_zero, mul_one, mul_neg_one, exp_zero]
  rw [mul_comm u ρ, mul_comm v ρ]
  ring

lemma separator_local {u v : ℝ} (hs : u^2+v^2 ≤ 1/100) :
    (35/100 : ℝ) * (1-ε) / 9 * (u^2+v^2) ≤
      FinProb.expect (tiltProb (u,v)) separator := by
  rw [separator_expect]
  have hz := Z_pos (u,v)
  have hzupper : Z (u,v) < (9:ℝ)/8 := by
    rw [Z_eq_cosh]
    have h := mul_lt_mul_of_pos_left (Z8_upper hs) w_pos
    have he := ε_lt_one
    rw [w_eq] at h ⊢
    nlinarith [ε_pos]
  have hn := N_lower hs
  have hnum := mul_le_mul_of_nonneg_left hn w_pos.le
  apply (le_div_iff₀ hz).mpr
  have ha : 0 ≤ (35/100 : ℝ)*(1-ε)/9*(u^2+v^2) := by
    have he : 0 < 1-ε := by linarith [ε_lt_one]
    positivity
  have hb := mul_le_mul_of_nonneg_left hzupper.le ha
  rw [w_eq] at hnum ⊢
  nlinarith

end BoundaryReduction.NinePoint
