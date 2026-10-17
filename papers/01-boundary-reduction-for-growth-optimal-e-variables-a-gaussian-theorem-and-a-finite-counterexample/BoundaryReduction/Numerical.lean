/-
Copyright (c) 2026. Explicit numerical constants used in Theorem 3.1
and Lemma A.1 of "Boundary reduction for growth-optimal e-variables".
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open Real

namespace BoundaryReduction.Numerical

noncomputable def ε : ℝ := 1 / 10 ^ 15

noncomputable def ρ : ℝ := 4 / (5 * Real.sqrt 2)

noncomputable def r₀ : ℝ := 1 / 100

theorem ε_pos : 0 < ε := by
  unfold ε; norm_num

theorem ε_eq_inv : ε = (10 : ℝ) ^ (-15 : ℤ) := by
  unfold ε
  norm_num [zpow_neg, zpow_ofNat]

theorem ε_lt_two : ε < 2 * (10 : ℝ) ^ (-15 : ℤ) := by
  rw [ε_eq_inv]
  norm_num [zpow_neg, zpow_ofNat]

theorem ε_lt_one : ε < 1 := by
  unfold ε; norm_num

theorem ε_div_one_sub_lt : ε / (1 - ε) < 2 * (10 : ℝ) ^ (-15 : ℤ) := by
  unfold ε
  norm_num [zpow_neg, zpow_ofNat]

theorem r₀_pos : 0 < r₀ := by
  unfold r₀; norm_num

theorem r₀_sq : r₀ ^ 2 = 1 / 10000 := by
  unfold r₀; norm_num

theorem r₀_eq_inv : r₀ = (10 : ℝ) ^ (-2 : ℤ) := by
  unfold r₀
  norm_num [zpow_neg, zpow_ofNat]

theorem ρ_pos : 0 < ρ := by
  unfold ρ; positivity

theorem ρ_sq : ρ ^ 2 = 8 / 25 := by
  unfold ρ
  rw [div_pow, mul_pow]
  have h : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [h]
  norm_num

theorem ρ_lt_one : ρ < 1 := by
  have h := ρ_sq
  have h2 : ρ ^ 2 < (1 : ℝ) ^ 2 := by rw [h]; norm_num
  have habs : |ρ| < |(1 : ℝ)| := sq_lt_sq.mp h2
  have hρ : 0 < ρ := ρ_pos
  rwa [abs_of_pos hρ, abs_of_pos (by norm_num : (0:ℝ) < 1)] at habs

theorem ρ_gt_half : (1 / 2 : ℝ) < ρ := by
  have h := ρ_sq
  have h2 : ((1 / 2 : ℝ)) ^ 2 = 1 / 4 := by norm_num
  have : ((1 / 2 : ℝ)) ^ 2 < ρ ^ 2 := by
    rw [h2, h]; norm_num
  have hρ : 0 < ρ := ρ_pos
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  have habs : |(1 / 2 : ℝ)| < |ρ| := sq_lt_sq.mp this
  rwa [abs_of_pos hhalf, abs_of_pos hρ] at habs

theorem ρ_lt_two_thirds : ρ < 2 / 3 := by
  have h := ρ_sq
  have h2 : ρ ^ 2 < ((2 / 3 : ℝ)) ^ 2 := by
    rw [h]; norm_num
  have hρ : 0 < ρ := ρ_pos
  have h23 : 0 < (2 / 3 : ℝ) := by norm_num
  have habs : |ρ| < |(2 / 3 : ℝ)| := sq_lt_sq.mp h2
  rwa [abs_of_pos hρ, abs_of_pos h23] at habs

theorem two_ρ_gt_one : (1 : ℝ) < 2 * ρ := by
  have h := ρ_gt_half
  linarith

theorem log_one_sub_eps_ge : Real.log (1 - ε) ≥ -ε / (1 - ε) := by
  have h1m : 0 < 1 - ε := by
    have : ε < 1 := ε_lt_one
    linarith
  have h := one_sub_inv_le_log_of_pos (x := 1 - ε) h1m
  have hform : 1 - (1 - ε)⁻¹ = -ε / (1 - ε) := by
    field_simp
    ring
  rw [← hform]
  exact h

theorem neg_log_one_sub_eps_le : -Real.log (1 - ε) ≤ ε / (1 - ε) := by
  have h := log_one_sub_eps_ge
  have h1m : 0 < 1 - ε := by
    have : ε < 1 := ε_lt_one
    linarith
  have : -ε / (1 - ε) = -(ε / (1 - ε)) := by ring
  rw [this] at h
  linarith

theorem seven_pow_thirteen_eq : (7 : ℝ) ^ 13 = 96889010407 := by
  norm_num

theorem rho_gt_113_over_200 : (113 / 200 : ℝ) < ρ := by
  have h := ρ_sq
  have h3 : ((113 / 200 : ℝ)) ^ 2 = 12769 / 40000 := by norm_num
  have h4 : (8 / 25 : ℝ) = 12800 / 40000 := by norm_num
  have h5 : ((113 / 200 : ℝ)) ^ 2 < 8 / 25 := by
    rw [h3, h4]; norm_num
  have h6 : ((113 / 200 : ℝ)) ^ 2 < ρ ^ 2 := by rw [h]; exact h5
  have hρ : 0 < ρ := ρ_pos
  have h113 : 0 < (113 / 200 : ℝ) := by norm_num
  have habs : |(113 / 200 : ℝ)| < |ρ| := sq_lt_sq.mp h6
  rwa [abs_of_pos h113, abs_of_pos hρ] at habs

theorem gamma_exposure_gap : (13 / 100 : ℝ) < 2 * ρ - 1 := by
  have h2 := rho_gt_113_over_200
  have hstep : (2 * (113 / 200 : ℝ) - 1) = 13 / 100 := by norm_num
  have hlt : (2 * (113 / 200 : ℝ) - 1) < 2 * ρ - 1 := by linarith
  rw [← hstep]
  exact hlt

end BoundaryReduction.Numerical
