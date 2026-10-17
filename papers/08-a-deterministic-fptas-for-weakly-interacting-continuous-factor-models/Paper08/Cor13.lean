import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Paper08.Basic
import Paper08.FPTAS

/-!
# Corollary 1.3 continued: the η ≥ 3 range conversion

`log(1+1/η) < 1/η` and `33/(20√η) ≤ 11√3/20 < 1` for `η ≥ 3`.
-/

noncomputable section

open scoped Real BigOperators

namespace Paper08
namespace FPTAS

/-- `log(1 + x) < x` for `x > 0`. -/
lemma log_one_add_inv_lt' {η : ℝ} (hη : 0 < η) :
    Real.log (1 + 1 / η) < 1 / η :=
  log_one_add_lt_self (x := 1 / η) (by positivity)

/-- `11√3/20 < 1`. -/
lemma eleven_sqrt3_over_twenty_lt_one :
    (11 / 20 : ℝ) * Real.sqrt 3 < 1 := by
  have hs : Real.sqrt 3 < 20 / 11 := by
    rw [Real.sqrt_lt (by norm_num) (by norm_num)]
    norm_num
  nlinarith [Real.sqrt_nonneg 3]

/-- `1/√η ≤ 1/√3` when `η ≥ 3`. -/
lemma inv_sqrt_le_inv_sqrt_three {η : ℝ} (hη : 3 ≤ η) :
    (Real.sqrt η)⁻¹ ≤ (Real.sqrt 3)⁻¹ := by
  have hs : Real.sqrt 3 ≤ Real.sqrt η := Real.sqrt_le_sqrt (by linarith)
  have h3 : (0:ℝ) < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  have hηp : (0:ℝ) < Real.sqrt η := Real.sqrt_pos.mpr (by linarith)
  exact (inv_le_inv₀ hηp h3).mpr hs

/-- The `η ≥ 3` chain: `33/(20√η) ≤ 11√3/20`. -/
lemma eta_ge_three_main {η : ℝ} (hη : 3 ≤ η) :
    (33 / 20) / Real.sqrt η ≤ (11 / 20) * Real.sqrt 3 := by
  have h1 : (Real.sqrt η : ℝ)⁻¹ ≤ (Real.sqrt 3)⁻¹ := inv_sqrt_le_inv_sqrt_three hη
  have hform : (33 / 20) / Real.sqrt η = (33 / 20) * (Real.sqrt η)⁻¹ := by
    rw [div_eq_mul_inv]
  rw [hform]
  have h2 : (33 / 20) * (Real.sqrt η)⁻¹ ≤ (33 / 20) * (Real.sqrt 3)⁻¹ :=
    mul_le_mul_of_nonneg_left h1 (by norm_num)
  have heq : (33 / 20) * (Real.sqrt 3)⁻¹ = (11 / 20) * Real.sqrt 3 := by
    have hsq : (Real.sqrt 3) ^ 2 = 3 := Real.sq_sqrt (by norm_num)
    field_simp
    nlinarith [Real.sqrt_nonneg 3, hsq]
  linarith

/-- Full `η ≥ 3` bound of Corollary 1.3. -/
lemma eta_ge_three_bound {η Δ : ℝ} (hη : 3 ≤ η) (hΔ : 1 ≤ Δ) :
    (11 / 10 : ℝ) * 3 * Δ * Real.sqrt η * (Real.log (1 + 1 / η) / (2 * Δ)) < 1 := by
  have hlog : Real.log (1 + 1 / η) < 1 / η :=
    log_one_add_inv_lt' (by linarith : 0 < η)
  have hpos : 0 < 2 * Δ := by nlinarith
  have hposη : 0 < η := by linarith
  have hform : (11 / 10 : ℝ) * 3 * Δ * Real.sqrt η * (Real.log (1 + 1 / η) / (2 * Δ))
      = (11 / 10) * (3 / 2) * Real.sqrt η * Real.log (1 + 1 / η) := by
    field_simp
  rw [hform]
  have hsp : 0 < (11 / 10 : ℝ) * (3 / 2) * Real.sqrt η := by positivity
  have hstep : (11 / 10 : ℝ) * (3 / 2) * Real.sqrt η * Real.log (1 + 1 / η)
      < (11 / 10) * (3 / 2) * Real.sqrt η * (1 / η) := by
    nlinarith [mul_pos hsp (by positivity : (0:ℝ) < 1 / η)]
  -- rewrite √η / η = 1/√η inside the right-hand side
  have hs : Real.sqrt η * (1 / η) = 1 / Real.sqrt η := by
    have hsq : (Real.sqrt η) ^ 2 = η := Real.sq_sqrt (le_of_lt hposη)
    field_simp
    nlinarith [Real.sqrt_nonneg η, hsq, hposη]
  have hrew : (11 / 10 : ℝ) * (3 / 2) * Real.sqrt η * (1 / η)
      = (11 / 10) * (3 / 2) * (1 / Real.sqrt η) := by
    calc (11 / 10 : ℝ) * (3 / 2) * Real.sqrt η * (1 / η)
        = (11 / 10) * (3 / 2) * (Real.sqrt η * (1 / η)) := by ring
      _ = (11 / 10) * (3 / 2) * (1 / Real.sqrt η) := by rw [hs]
  rw [hrew] at hstep
  have hfin : (11 / 10 : ℝ) * (3 / 2) * (1 / Real.sqrt η) = (33 / 20) / Real.sqrt η := by
    field_simp
    norm_num
  rw [hfin] at hstep
  have hcmp : (33 / 20) / Real.sqrt η ≤ (11 / 20) * Real.sqrt 3 :=
    eta_ge_three_main hη
  have hlt : (11 / 20 : ℝ) * Real.sqrt 3 < 1 := eleven_sqrt3_over_twenty_lt_one
  nlinarith

/-- The original range envelope (1.5). -/
def gamarnikSmediraRho (Δ η : ℕ) (δ : ℝ) : ℝ :=
  (1 - δ) ^ (1 / (2 * (Δ : ℝ))) *
    (1 + Real.log (1 + 1 / (η : ℝ)) / (2 * (Δ : ℝ)))

/-- The strict logarithmic range bound (A.1), obtained directly from (1.5). -/
theorem log_rho_lt {Δ η : ℕ} {δ : ℝ}
    (hΔ : 1 ≤ Δ) (hη : 1 ≤ η) (hδ : 0 < δ ∧ δ < 1) :
    Real.log (gamarnikSmediraRho Δ η δ) <
      Real.log (1 + 1 / (η : ℝ)) / (2 * (Δ : ℝ)) := by
  have hΔp : (0 : ℝ) < Δ := by exact_mod_cast (by omega : 0 < Δ)
  have hηp : (0 : ℝ) < η := by exact_mod_cast (by omega : 0 < η)
  have hbase : 0 < 1 - δ := by linarith [hδ.2]
  have hexp : 0 < (1 : ℝ) / (2 * (Δ : ℝ)) := by positivity
  have hp : 0 < (1 - δ) ^ (1 / (2 * (Δ : ℝ))) :=
    Real.rpow_pos_of_pos hbase _
  have hplt : (1 - δ) ^ (1 / (2 * (Δ : ℝ))) < 1 :=
    Real.rpow_lt_one hbase.le (by linarith [hδ.1]) hexp
  have hlog : 0 < Real.log (1 + 1 / (η : ℝ)) :=
    Real.log_pos (by have := one_div_pos.mpr hηp; linarith)
  have ht : 0 < Real.log (1 + 1 / (η : ℝ)) / (2 * (Δ : ℝ)) := by positivity
  have hρ : 0 < gamarnikSmediraRho Δ η δ := by
    unfold gamarnikSmediraRho
    positivity
  have hρlt : gamarnikSmediraRho Δ η δ <
      1 + Real.log (1 + 1 / (η : ℝ)) / (2 * (Δ : ℝ)) := by
    unfold gamarnikSmediraRho
    nlinarith
  exact lt_trans (Real.log_lt_log hρ hρlt) (log_one_add_lt_self ht)

/-- The two branches in Appendix A give the uniform slack `σ = 1/11`. -/
theorem gamarnikSmedira_regime {Δ η : ℕ} {δ : ℝ}
    (hΔ : 1 ≤ Δ) (hη : 2 ≤ η) (hδ : 0 < δ ∧ δ < 1) :
    3 * (Δ : ℝ) * Real.sqrt (η : ℝ) *
      Real.log (gamarnikSmediraRho Δ η δ) < 10 / 11 := by
  have hΔr : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hηr : (2 : ℝ) ≤ η := by exact_mod_cast hη
  have hq := log_rho_lt hΔ (by omega : 1 ≤ η) hδ
  have hscale : 0 < (11 / 10 : ℝ) * 3 * (Δ : ℝ) * Real.sqrt (η : ℝ) := by
    have hs : 0 < Real.sqrt (η : ℝ) := Real.sqrt_pos.mpr (by linarith)
    positivity
  have hstep := mul_lt_mul_of_pos_left hq hscale
  have hbound : (11 / 10 : ℝ) * 3 * (Δ : ℝ) * Real.sqrt (η : ℝ) *
      (Real.log (1 + 1 / (η : ℝ)) / (2 * (Δ : ℝ))) < 1 := by
    by_cases he : η = 2
    · subst η
      norm_num only [Nat.cast_ofNat]
      convert eta_two_bound hΔr using 1 <;> norm_num
    · exact eta_ge_three_bound (by exact_mod_cast (by omega : 3 ≤ η)) hΔr
  nlinarith

/-- The parameters supplied to Theorem 1.2 by Corollary 1.3 when `η ≥ 2`.
The remaining `η = 1` branch is the direct component algorithm of Lemma A.1. -/
def Params.ofGamarnikSmedira {Δ η : ℕ} {k δ : ℝ}
    (hΔ : 1 ≤ Δ) (hη : 2 ≤ η) (hk : 0 < k) (hδ : 0 < δ ∧ δ < 1)
    (hρ : 1 < gamarnikSmediraRho Δ η δ) : Params where
  r := η + 1
  c := Δ
  K := k
  q := Real.log (gamarnikSmediraRho Δ η δ)
  σ := 1 / 11
  r_ge := by omega
  c_ge := hΔ
  K_pos := hk
  q_pos := Real.log_pos hρ
  σ_range := sigma_choice
  regime := by
    have h := gamarnikSmedira_regime hΔ hη hδ
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right,
      show (1 : ℝ) - 1 / 11 = 10 / 11 by norm_num] using h.le

end FPTAS
end Paper08
