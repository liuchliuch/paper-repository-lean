import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import GeometricMedianCoresets.VarianceIdentity
import GeometricMedianCoresets.VarianceClose
import GeometricMedianCoresets.VarianceBoundary
import GeometricMedianCoresets.CostIdentity

/-!
# Inequality (8) and Markov for uniform sampling

`∑ ‖h_i - h̄‖² = ∑ ‖h_i‖² - n‖h̄‖² ≤ ∑ ‖h_i‖²`, hence
`variance ≤ (1/m)(1/n)∑ ‖h_i‖²`.

Markov: `a · #{I | a < f I} ≤ ∑ f I`, hence `bad ≤ Ef / a`.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets
namespace FinitePopulation

/-- `∑ ‖h_i - h̄‖² = ∑ ‖h_i‖² - n‖h̄‖²`. -/
theorem norm_sub_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    (u v : H) : ‖u - v‖ ^ 2 = ‖u‖ ^ 2 - 2 * ⟪u, v⟫ + ‖v‖ ^ 2 := by
  have h1 : ‖u - v‖ ^ 2 = ⟪u - v, u - v⟫ := (real_inner_self_eq_norm_sq _).symm
  have h2 : ⟪u - v, u - v⟫ = ⟪u, u⟫ - 2 * ⟪u, v⟫ + ⟪v, v⟫ :=
    real_inner_sub_sub_self u v
  have h3 : ⟪u, u⟫ = ‖u‖ ^ 2 := real_inner_self_eq_norm_sq u
  have h4 : ⟪v, v⟫ = ‖v‖ ^ 2 := real_inner_self_eq_norm_sq v
  rw [h1, h2, h3, h4]

theorem sum_centered_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (hn : 0 < n) (h : Fin n → H) :
    ∑ i, ‖h i - popMean h‖ ^ 2
      = (∑ i, ‖h i‖ ^ 2) - (n : ℝ) * ‖popMean h‖ ^ 2 := by
  rw [popMean_eq hn]
  set c : H := (n : ℝ)⁻¹ • (∑ j, h j)
  have hexpand : ∀ i, ‖h i - c‖ ^ 2 = ‖h i‖ ^ 2 - 2 * ⟪h i, c⟫ + ‖c‖ ^ 2 :=
    fun i => norm_sub_sq (h i) c
  rw [Finset.sum_congr rfl (fun i _ => hexpand i)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hlin : (∑ i, 2 * ⟪h i, c⟫) = 2 * ⟪∑ i, h i, c⟫ := by
    rw [← Finset.mul_sum, sum_inner]
  rw [hlin]
  have hconst : ∑ _i : Fin n, ‖c‖ ^ 2 = (n : ℝ) * ‖c‖ ^ 2 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [hconst]
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hsum : ∑ i, h i = (n : ℝ) • c := by
    rw [smul_smul, mul_inv_cancel₀ hn0, one_smul]
  rw [hsum]
  have : 2 * ⟪(n : ℝ) • c, c⟫ = 2 * (n : ℝ) * ⟪c, c⟫ := by
    rw [real_inner_smul_left]
    ring
  rw [this]
  have : ⟪c, c⟫ = ‖c‖ ^ 2 := real_inner_self_eq_norm_sq c
  rw [this]
  ring

/-- `∑ ‖h_i - h̄‖² ≤ ∑ ‖h_i‖²`. -/
theorem sum_centered_sq_le {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (hn : 0 < n) (h : Fin n → H) :
    ∑ i, ‖h i - popMean h‖ ^ 2 ≤ ∑ i, ‖h i‖ ^ 2 := by
  rw [sum_centered_sq hn h]
  have hnonneg : 0 ≤ (n : ℝ) * ‖popMean h‖ ^ 2 := by positivity
  linarith

/-- Inequality (8): `variance ≤ (1/m)(1/n)∑ ‖h_i - h̄‖²` for `2 ≤ m < n`. -/
theorem variance_le_avg_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hmn : m < n) (h : Fin n → H) :
    uniformAvg (m := m) (fun I => ‖sampleMean h I - popMean h‖ ^ 2)
      ≤ ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i - popMean h‖ ^ 2 := by
  rw [variance_identity_m_ge_2 hn hm hmn h]
  have hS : 0 ≤ ∑ i, ‖h i - popMean h‖ ^ 2 := by positivity
  have hm0 : (0:ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hn1 : (0:ℝ) < n - 1 := by
    have : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    nlinarith
  have hnm : (0:ℝ) < n - m := by
    have : (m:ℝ) < n := by exact_mod_cast hmn
    nlinarith
  have hfrac : (n - m : ℝ) / (m * (n - 1) : ℝ) ≤ (1:ℝ) / m := by
    have hm2 : (2:ℝ) ≤ m := by exact_mod_cast hm
    have h1 : (n - m : ℝ) ≤ n - 1 := by nlinarith
    have h2 : (0:ℝ) < m * (n - 1) := by nlinarith
    have h3 : (n - m : ℝ) / (m * (n - 1) : ℝ) ≤ (n - 1 : ℝ) / (m * (n - 1) : ℝ) :=
      div_le_div_of_nonneg_right h1 (by nlinarith)
    have h4 : (n - 1 : ℝ) / (m * (n - 1) : ℝ) = (1:ℝ) / m := by
      field_simp
    linarith
  have hinv : (0:ℝ) ≤ 1 / n := by
    exact div_nonneg (by norm_num) (le_of_lt hn0)
  have h1 : (n - m : ℝ) / (m * (n - 1) : ℝ) ≤ (1:ℝ) / m := hfrac
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right h1 hinv) hS

/-- Markov on the uniform `m`-subset law. -/
theorem markov_uniform {n m : ℕ} (a : ℝ) (ha : 0 < a)
    (f : (Finset (Fin n)) → ℝ) (hf : ∀ I, 0 ≤ f I) :
    ((Finset.univ : Finset (Fin n)).powersetCard m |>.filter
        (fun I => a < f I)).card
      ≤ (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I) / a := by
  classical
  have hcount : ((Finset.univ : Finset (Fin n)).powersetCard m |>.filter
      (fun I => a < f I)).card * a
      ≤ ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I := by
    have hle : ∀ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (if a < f I then (a:ℝ) else 0) ≤ f I := by
      intro I _
      by_cases hh : a < f I
      · simp [hh]
        exact le_of_lt hh
      · simp [hh]
        exact hf I
    have hsum := Finset.sum_le_sum hle
    rw [Finset.sum_ite] at hsum
    simp at hsum
    have h2 : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m with a < f I, a)
        = ((Finset.univ : Finset (Fin n)).powersetCard m |>.filter
            (fun I => a < f I)).card * a := by
      rw [Finset.sum_const, nsmul_eq_mul]
    linarith
  have ha0 : (0:ℝ) < a := ha
  have : ((Finset.univ : Finset (Fin n)).powersetCard m |>.filter
      (fun I => a < f I)).card ≤
      (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, f I) / a := by
    rw [le_div_iff₀ ha]
    exact hcount
  exact this


/-- Inequality (8) in full range `1 ≤ m ≤ n`, `n ≥ 1`, chained to the raw second moment:
`variance ≤ (1/m)(1/n)∑ ‖h_i‖²`. -/
theorem frac_le_real {n m : ℝ} (hm : 2 ≤ m) (hmn : m < n) (_hn : 2 ≤ n) :
    (n - m) / (m * (n - 1)) ≤ 1 / m := by
  have h1 : n - m ≤ n - 1 := by nlinarith
  have h2 : 0 < m * (n - 1) := by nlinarith
  have h3 : (n - m) / (m * (n - 1)) ≤ (n - 1) / (m * (n - 1)) :=
    div_le_div_of_nonneg_right h1 (le_of_lt h2)
  have h4 : (n - 1) / (m * (n - 1)) = 1 / m := by
    have hn1 : n - 1 ≠ 0 := by nlinarith
    have hm0 : m ≠ 0 := by nlinarith
    field_simp
  linarith

theorem variance_le_raw_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (h : Fin n → H) :
    uniformAvg (m := m) (fun I => ‖sampleMean h I - popMean h‖ ^ 2)
      ≤ ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2 := by
  by_cases h1 : n = 1
  · subst h1
    have hm1 : m = 1 := by omega
    subst hm1
    rw [variance_one_point h]
    positivity
  by_cases h2 : m = n
  · subst h2
    rw [variance_zero_of_eq hn h]
    positivity
  by_cases h3 : m = 1
  · subst h3
    rw [variance_one_sample hn h]
    have hraw : ∑ i, ‖h i - popMean h‖ ^ 2 ≤ ∑ i, ‖h i‖ ^ 2 :=
      sum_centered_sq_le hn h
    have hnn : (0:ℝ) ≤ (1:ℝ) / n := div_nonneg (by norm_num) (Nat.cast_nonneg _)
    have hstep : ((1:ℝ) / n) * ∑ i, ‖h i - popMean h‖ ^ 2
        ≤ ((1:ℝ) / 1) * ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2 := by
      have h1' : ((1:ℝ) / n) * ∑ i, ‖h i - popMean h‖ ^ 2
          ≤ ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2 := mul_le_mul_of_nonneg_left hraw hnn
      have h2' : ((1:ℝ) / 1) * ((1:ℝ) / n) = ((1:ℝ) / n) := by norm_num
      rw [h2']
      exact h1'
    simpa [Nat.cast_one] using hstep
  have hn2 : 2 ≤ n := by omega
  have hm2 : 2 ≤ m := by omega
  have hmn2 : m < n := by omega
  rw [variance_identity_m_ge_2 hn2 hm2 hmn2 h]
  have hraw : ∑ i, ‖h i - popMean h‖ ^ 2 ≤ ∑ i, ‖h i‖ ^ 2 :=
    sum_centered_sq_le hn h
  have hfrac : ((n - m : ℝ) / ((m:ℝ) * ((n:ℝ) - 1))) ≤ (1:ℝ) / m := by
    have hm2r : (2:ℝ) ≤ m := by exact_mod_cast hm2
    have hmn2r : (m:ℝ) < n := by exact_mod_cast hmn2
    have hn2r : (2:ℝ) ≤ n := by exact_mod_cast hn2
    exact frac_le_real hm2r hmn2r hn2r
  have hpos : (0:ℝ) ≤ (1:ℝ) / n := div_nonneg (by norm_num) (Nat.cast_nonneg _)
  have hstep1 : ((n - m : ℝ) / ((m:ℝ) * ((n:ℝ) - 1))) * ((1:ℝ) / n)
      * ∑ i, ‖h i - popMean h‖ ^ 2
      ≤ ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i - popMean h‖ ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hfrac hpos) (by positivity)
  have hstep2 : ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i - popMean h‖ ^ 2
      ≤ ((1:ℝ) / m) * ((1:ℝ) / n) * ∑ i, ‖h i‖ ^ 2 :=
    mul_le_mul_of_nonneg_left hraw
      (mul_nonneg
        (div_nonneg (by norm_num) (by exact_mod_cast (le_of_lt hm)))
        (div_nonneg (by norm_num) (Nat.cast_nonneg _)))
  exact le_trans hstep1 hstep2

end FinitePopulation
end GeometricMedianCoresets
