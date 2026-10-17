import Paper14.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Return time `τ = 1/(ab)` and its mean

Paper anchors: E1 (`τ(a,b)=1/(ab)`, `∫_Ω τ dm = π²/3`), E4 (`H_{r,n}/n → π²/3`).

We prove the concrete integral identity of E1
`2 ∫_{0}^{1} (-log(1-a))/a da = π²/3`
by the power series `-log(1-a) = ∑_{n≥0} a^{n+1}/(n+1)`, so
`(-log(1-a))/a = ∑_{n≥0} a^n/(n+1)` and `∫_0^1 a^n/(n+1) da = 1/(n+1)²`,
whose sum is `∑ 1/n² = π²/6`.

We also record `τ > 0` on `Ω`, measurability of `Ω`, and the Fubini inner
slice `∫_b τ(a,b) db = (-log(1-a))/a` for `a ∈ (0,1)`. The remaining Fubini
step identifying `∫_Ω τ dm` with this rectangular integral is left to the
reader (`m = 2 da db`, so the two forms of E1 agree once Fubini is applied).
-/
open MeasureTheory Filter Topology Set Real
open scoped Interval

namespace Paper14

/-- Paper E1, concrete form: `2 ∫_0^1 (-log(1-a))/a da = π²/3`. -/
def MeanReturnTimeStatement : Prop :=
  (2 : ℝ) * ∫ a in Set.Ioo (0:ℝ) 1, (-Real.log (1 - a)) / a = π ^ 2 / 3

/-- Coordinate form of paper E1 (same identity). -/
def MeanReturnTimeIntegralStatement : Prop :=
  (2 : ℝ) * ∫ a in Set.Ioo (0:ℝ) 1, (-Real.log (1 - a)) / a = π ^ 2 / 3

/-! ## Positivity of `τ` on `Ω` -/

theorem tau_pos_on_Omega {x : ℝ × ℝ} (hx : x ∈ Omega) : 0 < tau x := by
  rcases mem_Omega.1 hx with ⟨ha0, _, hb0, _, _⟩
  rw [tau_apply]
  exact one_div_pos.2 (mul_pos ha0 hb0)

theorem tau_pos_of_mem (a b : ℝ) (h : (a, b) ∈ Omega) : 0 < tau (a, b) :=
  tau_pos_on_Omega h

/-! ## Power series for `-log(1-a)/a` -/

/-- On `(0,1)`, `(-log(1-a))/a = ∑' n, a^n/(n+1)`. -/
theorem neg_log_one_sub_div_eq_tsum (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (-Real.log (1 - a)) / a = ∑' n : ℕ, a ^ n / ((n : ℝ) + 1) := by
  have hlt : |a| < 1 := by
    rw [abs_of_pos ha0]
    exact ha1
  have ha : a ≠ 0 := ne_of_gt ha0
  have hsum := hasSum_pow_div_log_of_abs_lt_one hlt
  have hterm : ∀ n : ℕ, a ^ (n + 1) / ((n : ℝ) + 1) = (a ^ n / ((n : ℝ) + 1)) * a := by
    intro n
    rw [pow_succ a n]
    field_simp
  have key : (fun n : ℕ => a ^ n / ((n : ℝ) + 1))
      = (fun n : ℕ => a ^ (n + 1) / ((n : ℝ) + 1) * a⁻¹) := by
    funext n
    rw [hterm n]
    field_simp [ha]
  rw [← hsum.tsum_eq, key, tsum_mul_right]
  exact div_eq_mul_inv _ _

/-! ## Integral of `a^n` on `Ioo 0 1` -/

theorem integral_pow_Ioo_zero_one (n : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, x ^ n = 1 / ((n : ℝ) + 1) := by
  have h01 : (0:ℝ) ≤ 1 := zero_le_one
  have h : (∫ x in (0:ℝ)..1, x ^ n) = ∫ x in Ioo (0:ℝ) 1, x ^ n := by
    rw [intervalIntegral.integral_of_le h01, integral_Ioc_eq_integral_Ioo]
  rw [← h, integral_pow]
  have h1 : (1:ℝ) ^ (n + 1) = 1 := one_pow _
  have h2 : (0:ℝ) ^ (n + 1) = 0 := zero_pow (by omega : (n + 1 : ℕ) ≠ 0)
  rw [h1, h2, sub_zero]

theorem integral_pow_div_Ioo_zero_one (n : ℕ) :
    ∫ x in Ioo (0:ℝ) 1, x ^ n / ((n : ℝ) + 1) = 1 / (((n : ℝ) + 1) ^ 2) := by
  rw [integral_div, integral_pow_Ioo_zero_one]
  have h : (1 / ((n : ℝ) + 1)) / ((n : ℝ) + 1) = 1 / (((n : ℝ) + 1) ^ 2) := by
    rw [div_div, ← sq]
  exact h

/-! ## Summability and reindexing -/

theorem summable_one_div_sq_succ : Summable (fun n : ℕ => (1:ℝ) / (((n : ℝ) + 1) ^ 2)) := by
  have hs : Summable (fun k : ℕ => (1:ℝ) / ((k : ℝ) ^ 2)) := hasSum_zeta_two.summable
  have heq : (fun n : ℕ => (1:ℝ) / (((n : ℝ) + 1) ^ 2))
      = fun n : ℕ => (1:ℝ) / ((((n + 1 : ℕ) : ℝ) ^ 2)) := by
    funext n; push_cast; rfl
  rw [heq]
  refine hs.comp_injective (fun n m h => ?_)
  omega

theorem tsum_one_div_sq_succ : ∑' n : ℕ, (1:ℝ) / (((n : ℝ) + 1) ^ 2) = π ^ 2 / 6 := by
  have hs : Summable (fun k : ℕ => (1:ℝ) / ((k : ℝ) ^ 2)) := hasSum_zeta_two.summable
  have hsplit : (∑' k : ℕ, (1:ℝ) / ((k : ℝ) ^ 2))
      = (1:ℝ) / (((0:ℕ) : ℝ) ^ 2) + ∑' n : ℕ, (1:ℝ) / (((n + 1 : ℕ) : ℝ) ^ 2) :=
    hs.tsum_eq_zero_add
  have h0 : (1:ℝ) / (((0:ℕ) : ℝ) ^ 2) = 0 := by norm_num
  have heq : (fun n : ℕ => (1:ℝ) / (((n : ℝ) + 1) ^ 2))
      = fun n : ℕ => (1:ℝ) / ((((n + 1 : ℕ) : ℝ) ^ 2)) := by
    funext n; push_cast; rfl
  rw [heq]
  calc ∑' n : ℕ, (1:ℝ) / ((((n + 1 : ℕ) : ℝ) ^ 2))
      = (1:ℝ) / (((0:ℕ) : ℝ) ^ 2) + ∑' n : ℕ, (1:ℝ) / ((((n + 1 : ℕ) : ℝ) ^ 2)) := by
          rw [h0, zero_add]
    _ = ∑' k : ℕ, (1:ℝ) / ((k : ℝ) ^ 2) := hsplit.symm
    _ = π ^ 2 / 6 := hasSum_zeta_two.tsum_eq

/-! ## The rectangular integral identity -/

theorem integral_neg_log_one_sub_div_eq :
    ∫ a in Ioo (0:ℝ) 1, (-Real.log (1 - a)) / a = π ^ 2 / 6 := by
  set μ : Measure ℝ := volume.restrict (Ioo (0:ℝ) 1) with hμ
  have hpt : ∀ a ∈ Ioo (0:ℝ) 1, (-Real.log (1 - a)) / a = ∑' n : ℕ, a ^ n / ((n : ℝ) + 1) := by
    intro a ha
    exact neg_log_one_sub_div_eq_tsum a ha.1 ha.2
  have hae : ∀ᵐ a ∂μ, (-Real.log (1 - a)) / a = ∑' n : ℕ, a ^ n / ((n : ℝ) + 1) := by
    rw [hμ]
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
    exact hpt a ha
  have hI : ∫ a in Ioo (0:ℝ) 1, (-Real.log (1 - a)) / a
      = ∫ a, (-Real.log (1 - a)) / a ∂μ := rfl
  rw [hI, integral_congr_ae hae]
  have hFn : ∀ n : ℕ, Integrable (fun a : ℝ => a ^ n / ((n : ℝ) + 1)) μ := by
    intro n
    have hcont : Continuous (fun a : ℝ => a ^ n / ((n : ℝ) + 1)) :=
      (continuous_pow n).div_const _
    have hcc : IntegrableOn (fun a : ℝ => a ^ n / ((n : ℝ) + 1)) (Icc (0:ℝ) 1) :=
      hcont.integrableOn_Icc
    have hioo : IntegrableOn (fun a : ℝ => a ^ n / ((n : ℝ) + 1)) (Ioo (0:ℝ) 1) := by
      rw [← integrableOn_Icc_iff_integrableOn_Ioo]
      exact hcc
    rw [hμ]
    exact hioo
  have hnorm : ∀ n : ℕ, ∫ a, ‖a ^ n / ((n : ℝ) + 1)‖ ∂μ = 1 / (((n : ℝ) + 1) ^ 2) := by
    intro n
    have h : (fun a : ℝ => ‖a ^ n / ((n : ℝ) + 1)‖) =ᵐ[μ]
        (fun a => a ^ n / ((n : ℝ) + 1)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
      rw [Real.norm_of_nonneg]
      exact div_nonneg (pow_nonneg ha.1.le n) (by positivity)
    rw [integral_congr_ae h, hμ]
    exact integral_pow_div_Ioo_zero_one n
  have hsum : Summable (fun n : ℕ => ∫ a, ‖a ^ n / ((n : ℝ) + 1)‖ ∂μ) := by
    simp_rw [hnorm]
    exact summable_one_div_sq_succ
  rw [← integral_tsum_of_summable_integral_norm hFn hsum]
  have hInt : ∀ n : ℕ, ∫ a, a ^ n / ((n : ℝ) + 1) ∂μ = 1 / (((n : ℝ) + 1) ^ 2) := by
    intro n
    rw [hμ]
    exact integral_pow_div_Ioo_zero_one n
  simp_rw [hInt]
  exact tsum_one_div_sq_succ

/-- Paper E1: `2 ∫_0^1 (-log(1-a))/a da = π²/3`. -/
theorem MeanReturnTimeIntegral : MeanReturnTimeIntegralStatement := by
  rw [MeanReturnTimeIntegralStatement, integral_neg_log_one_sub_div_eq]
  ring

/-- Paper E1 concrete identity (same statement, paper's name). -/
theorem MeanReturnTime : MeanReturnTimeStatement := by
  rw [MeanReturnTimeStatement, integral_neg_log_one_sub_div_eq]
  ring

/-! ## Measurability of `Ω` and the Fubini inner slice -/

theorem measurableSet_Omega : MeasurableSet Omega := by
  have h : Omega = {x : ℝ × ℝ | 0 < x.1} ∩ {x | x.1 ≤ 1} ∩ {x | 0 < x.2} ∩ {x | x.2 ≤ 1}
      ∩ {x | (1:ℝ) < x.1 + x.2} := by
    ext x
    simp only [mem_inter_iff, mem_setOf_eq]
    constructor
    · intro hx
      rcases mem_Omega.1 hx with ⟨h1, h2, h3, h4, h5⟩
      exact ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
    · intro hx
      rcases hx with ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩
      exact mem_Omega.2 ⟨h1, h2, h3, h4, h5⟩
  rw [h]
  exact (((((measurableSet_lt measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_const)).inter
        (measurableSet_lt measurable_const measurable_snd)).inter
          (measurableSet_le measurable_snd measurable_const)).inter
            (measurableSet_lt measurable_const (measurable_fst.add measurable_snd)))

/-- Slice of `τ` along `b` at fixed `a`. -/
noncomputable def tauSlice (a : ℝ) : ℝ → ℝ :=
  fun b => Set.indicator Omega (fun _ => 1 / (a * b)) (a, b)

theorem tauSlice_apply (a b : ℝ) :
    tauSlice a b = Set.indicator Omega (fun _ => 1 / (a * b)) (a, b) := rfl

theorem tauSlice_apply_if (a b : ℝ) [Decidable ((a, b) ∈ Omega)] :
    tauSlice a b = if (a, b) ∈ Omega then 1 / (a * b) else 0 := by
  rw [tauSlice_apply]
  by_cases h : (a, b) ∈ Omega
  · rw [Set.indicator_of_mem h, if_pos h]
  · rw [Set.indicator_of_notMem h, if_neg h]

/-- On `0 < a < 1`, `Ω`-membership of `(a,b)` is `1-a < b ≤ 1`. -/
theorem mem_Omega_iff_of_a (a b : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    (a, b) ∈ Omega ↔ 1 - a < b ∧ b ≤ 1 := by
  constructor
  · intro hx
    rcases mem_Omega.1 hx with ⟨_, _, _, hb1, hsum⟩
    exact ⟨by linarith, hb1⟩
  · intro ⟨hlo, hhi⟩
    refine mem_Omega.2 ⟨ha0, le_of_lt ha1, by linarith, hhi, by linarith⟩

/-- Inner integral of `τ` over `b` for `0 < a < 1`: equals `(-log(1-a))/a`. -/
theorem integral_tauSlice (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ∫ b, tauSlice a b = (-Real.log (1 - a)) / a := by
  classical
  have hmem : ∀ b : ℝ, ((a, b) ∈ Omega) ↔ (1 - a < b ∧ b ≤ 1) :=
    fun b => mem_Omega_iff_of_a a b ha0 ha1
  have h0 : tauSlice a = fun b => if 1 - a < b ∧ b ≤ 1 then 1 / (a * b) else 0 := by
    funext b
    rw [tauSlice_apply_if a b]
    simp_rw [hmem b]
  rw [h0]
  have hIoc : (fun b : ℝ => if 1 - a < b ∧ b ≤ 1 then 1 / (a * b) else 0)
      = (Ioc (1 - a) 1).indicator (fun b => 1 / (a * b)) := by
    funext b
    by_cases hb : 1 - a < b ∧ b ≤ 1
    · rw [if_pos hb, Set.indicator_of_mem]
      exact hb
    · rw [if_neg hb, Set.indicator_of_notMem]
      exact hb
  rw [hIoc, integral_indicator (measurableSet_Ioc)]
  have hmul : ∀ b : ℝ, 1 / (a * b) = (1 / a) * (1 / b) := by
    intro b
    field_simp
  simp_rw [hmul, integral_const_mul]
  have h1 : 0 < 1 - a := by linarith
  have h1le : (1 - a : ℝ) ≤ 1 := by linarith
  have hinner : ∫ x in Ioc (1 - a) 1, 1 / x = ∫ x in (1 - a)..1, 1 / x :=
    (intervalIntegral.integral_of_le h1le).symm
  rw [hinner, integral_one_div_of_pos h1 (by norm_num : (0:ℝ) < 1)]
  have hlog : Real.log (1 / (1 - a)) = -Real.log (1 - a) := by
    rw [one_div, Real.log_inv]
  rw [hlog, div_eq_mul_inv]
  ring

/-- Outer integrand vanishes for `a ≤ 0`. -/
theorem integral_tauSlice_of_le_zero (a : ℝ) (ha : a ≤ 0) :
    ∫ b, tauSlice a b = 0 := by
  classical
  have h : tauSlice a = fun _ => 0 := by
    funext b
    have hnot : ¬((a, b) ∈ Omega) := by
      intro hx
      rcases mem_Omega.1 hx with ⟨ha0, _, _, _, _⟩
      exact absurd ha0 (not_lt.mpr ha)
    rw [tauSlice_apply_if, if_neg hnot]
  rw [h, integral_zero]

/-- Outer integrand vanishes for `a > 1`. -/
theorem integral_tauSlice_of_one_lt (a : ℝ) (ha : 1 < a) :
    ∫ b, tauSlice a b = 0 := by
  classical
  have h : tauSlice a = fun _ => 0 := by
    funext b
    have hnot : ¬((a, b) ∈ Omega) := by
      intro hx
      rcases mem_Omega.1 hx with ⟨_, ha1, _, _, _⟩
      exact absurd ha1 (not_le.mpr ha)
    rw [tauSlice_apply_if, if_neg hnot]
  rw [h, integral_zero]

/-- Almost everywhere on `(0,1)`, the inner integral of `τ` is `(-log(1-a))/a`. -/
theorem ae_integral_tauSlice :
    (fun a : ℝ => ∫ b, tauSlice a b)
      =ᵐ[volume.restrict (Ioo (0:ℝ) 1)] (fun a => (-Real.log (1 - a)) / a) := by
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with a ha
  exact integral_tauSlice a ha.1 ha.2

end Paper14
