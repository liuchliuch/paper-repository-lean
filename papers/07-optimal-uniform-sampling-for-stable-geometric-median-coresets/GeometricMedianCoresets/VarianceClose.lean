import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import GeometricMedianCoresets.VarianceCount
import GeometricMedianCoresets.VarianceDoubleSum
import GeometricMedianCoresets.VarianceIdentity
import GeometricMedianCoresets.VarianceBinomial

/-!
# Lemma 2.3 (7): finite-population variance

For `h : Fin n → H` in a real Hilbert space, `w_i = h_i - h̄`, `2 ≤ m < n`, `n ≥ 2`,

  `uniformAvg (fun I => ‖sampleMean h I - popMean h‖²)
    = (n-m)/(m(n-1)) · (1/n) · ∑ i, ‖w_i‖²`.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets
namespace FinitePopulation

/-- Off-diagonal inner-product sum via `∑ w_i = 0`. -/
theorem sum_offDiag_inner_eq_neg {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n : ℕ} (hn : 1 < n) (w : Fin n → H) (hw : ∑ i, w i = 0) :
    (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ⟪w i, w j⟫)
      = -∑ i, ⟪w i, w i⟫ := by
  have hall : (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin n)), ⟪w i, w j⟫)
      = ⟪∑ i, w i, ∑ j, w j⟫ := by
    rw [sum_inner]
    exact Finset.sum_congr rfl fun i _ =>
      (inner_sum (Finset.univ : Finset (Fin n)) w (w i)).symm
  have hzero : ⟪∑ i, w i, ∑ j, w j⟫ = 0 := by rw [hw, inner_zero_right]
  have hsplit : ∀ i : Fin n,
      (∑ j ∈ (Finset.univ : Finset (Fin n)), ⟪w i, w j⟫)
        = ⟪w i, w i⟫ + ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ⟪w i, w j⟫ :=
    fun i => VarianceDoubleSum.sum_univ_split i (fun j => ⟪w i, w j⟫)
  have hsplit_sum : (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin n)), ⟪w i, w j⟫)
      = (∑ i, ⟪w i, w i⟫) + ∑ i, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ⟪w i, w j⟫ := by
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib]
  rw [hall, hzero] at hsplit_sum
  linarith

/-- Specialization of the double-sum count to inner products. -/
theorem double_sum_inner {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hm : 2 ≤ m) (hmn : m ≤ n) (w : Fin n → H) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ‖∑ i ∈ I, w i‖ ^ 2)
      = (n - 1).choose (m - 1) * (∑ i, ⟪w i, w i⟫)
        + (n - 2).choose (m - 2) * (∑ i, ∑ j ∈ (Finset.univ : Finset (Fin n)).erase i, ⟪w i, w j⟫) := by
  have h : ∀ I : Finset (Fin n), ‖∑ i ∈ I, w i‖ ^ 2
      = ∑ i ∈ I, ∑ j ∈ I, ⟪w i, w j⟫ :=
    fun I => norm_sum_sq_eq_double_sum w I
  rw [Finset.sum_congr rfl (fun I _ => h I)]
  exact VarianceDoubleSum.sum_double_mem_mem (fun i j => ⟪w i, w j⟫) hm hmn

/-- After `∑ w = 0`, the double sum collapses to a single diagonal. -/
theorem double_sum_inner_collapse {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 1 < n) (hm : 2 ≤ m) (hmn : m ≤ n)
    (w : Fin n → H) (hw : ∑ i, w i = 0) :
    (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ‖∑ i ∈ I, w i‖ ^ 2)
      = ((n - 1).choose (m - 1) - (n - 2).choose (m - 2)) * (∑ i, ‖w i‖ ^ 2) := by
  rw [double_sum_inner hm hmn w, sum_offDiag_inner_eq_neg hn w hw]
  have hdiag : ∀ i, ⟪w i, w i⟫ = ‖w i‖ ^ 2 := fun i => real_inner_self_eq_norm_sq _
  rw [Finset.sum_congr rfl (fun i _ => hdiag i)]
  ring

/-- `C(n-1,m-1) - C(n-2,m-2) = C(n,m)·m(n-m)/(n(n-1))` for `2 ≤ m < n`. -/
theorem bin_diff (n m : ℕ) (hn : 2 ≤ n) (hm : 2 ≤ m) (hmn : m < n) :
    ((n - 1).choose (m - 1) : ℝ) - ((n - 2).choose (m - 2) : ℝ)
      = (n.choose m : ℝ) * (m * (n - m)) / (n * (n - 1)) := by
  have hmn2 : m ≤ n := by omega
  have h1 : n.choose m * m = (n - 1).choose (m - 1) * n :=
    VarianceBinomial.choose_mul_eq_choose_pred n m (by omega) hmn2
  have h2 : n.choose m * (m * (m - 1)) = (n - 2).choose (m - 2) * (n * (n - 1)) :=
    VarianceBinomial.choose_mul_eq_choose_pred_pred n m (by omega) hmn2
  have h1r : (n.choose m : ℝ) * (m : ℝ)
      = ((n - 1).choose (m - 1) : ℝ) * (n : ℝ) := by
    exact_mod_cast h1
  have h2r : (n.choose m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1))
      = ((n - 2).choose (m - 2) : ℝ) * ((n : ℝ) * ((n : ℝ) - 1)) := by
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have hn1 : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    have h2r0 : (n.choose m : ℝ) * ((m : ℝ) * ((m - 1 : ℕ) : ℝ))
        = ((n - 2).choose (m - 2) : ℝ) * ((n : ℝ) * ((n - 1 : ℕ) : ℝ)) := by
      exact_mod_cast h2
    rw [hm1, hn1] at h2r0
    exact h2r0
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hn1r : (n : ℝ) - 1 ≠ 0 := by
    have : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    nlinarith
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hA : ((n - 1).choose (m - 1) : ℝ) = (n.choose m : ℝ) * (m : ℝ) / (n : ℝ) := by
    field_simp at h1r ⊢
    nlinarith
  have hB : ((n - 2).choose (m - 2) : ℝ)
      = (n.choose m : ℝ) * ((m : ℝ) * ((m : ℝ) - 1)) / ((n : ℝ) * ((n : ℝ) - 1)) := by
    field_simp at h2r ⊢
    nlinarith
  rw [hA, hB]
  field_simp
  ring_nf

/-- On `m`-subsets, `h̄_I - h̄ = (1/m) ∑_{i∈I} w_i`. -/
theorem sampleMean_err_eq {H : Type*} [NormedAddCommGroup H] [Module ℝ H]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : Fin n → H)
    (I : Finset (Fin n)) (hI : I.card = m) :
    sampleMean h I - popMean h = (m : ℝ)⁻¹ • ∑ i ∈ I, centered h i := by
  have hIpos : 0 < I.card := by rw [hI]; exact hm
  have := sampleMean_sub_popMean hn h I hIpos
  rw [hI] at this
  exact this

/-- `‖h̄_I - h̄‖² = m^{-2} ‖∑_{i∈I} w_i‖²` on `m`-subsets. -/
theorem sampleMean_err_sq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : Fin n → H)
    (I : Finset (Fin n)) (hI : I.card = m) :
    ‖sampleMean h I - popMean h‖ ^ 2
      = (m : ℝ)⁻¹ ^ 2 * ‖∑ i ∈ I, centered h i‖ ^ 2 := by
  rw [sampleMean_err_eq hn hm h I hI]
  have : ‖(m : ℝ)⁻¹ • ∑ i ∈ I, centered h i‖ ^ 2
      = ((m : ℝ)⁻¹ ^ 2) * ‖∑ i ∈ I, centered h i‖ ^ 2 := by
    rw [norm_smul, Real.norm_eq_abs, mul_pow]
    have hpos : (0:ℝ) ≤ (m : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
    rw [abs_of_nonneg hpos]
  exact this

/-- Lemma 2.3 (7) for `2 ≤ m < n` and `n ≥ 2`. -/
theorem variance_identity_m_ge_2 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) (hmn : m < n)
    (h : Fin n → H) :
    uniformAvg (m := m) (fun I => ‖sampleMean h I - popMean h‖ ^ 2)
      = ((n - m : ℝ) / (m * (n - 1) : ℝ)) * ((1:ℝ) / n) * ∑ i, ‖centered h i‖ ^ 2 := by
  have hn0 : 0 < n := by omega
  have hm0 : 0 < m := by omega
  have hmn2 : m ≤ n := by omega
  have havg : uniformAvg (m := m) (fun I => ‖sampleMean h I - popMean h‖ ^ 2)
      = (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ‖sampleMean h I - popMean h‖ ^ 2) / (n.choose m : ℝ) := rfl
  rw [havg]
  have hcard : ∀ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m, I.card = m := by
    intro I hI
    exact (Finset.mem_powersetCard.1 hI).2
  have hsum : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ‖sampleMean h I - popMean h‖ ^ 2)
      = ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ((m : ℝ)⁻¹ ^ 2 * ‖∑ i ∈ I, centered h i‖ ^ 2) :=
    Finset.sum_congr rfl fun I hI => sampleMean_err_sq hn0 hm0 h I (hcard I hI)
  rw [hsum]
  have hfactor : (∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      ((m : ℝ)⁻¹ ^ 2 * ‖∑ i ∈ I, centered h i‖ ^ 2))
      = (m : ℝ)⁻¹ ^ 2 * ∑ I ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
          ‖∑ i ∈ I, centered h i‖ ^ 2 := by
    rw [← Finset.mul_sum]
  rw [hfactor, double_sum_inner_collapse hn hm hmn2 (centered h) (sum_centered hn0 h)]
  have hbin := bin_diff n m hn hm hmn
  rw [hbin]
  have hm0r : (m : ℝ) ≠ 0 := by exact_mod_cast hm0.ne'
  have hC : (n.choose m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : m ≤ n)).ne'
  have hN1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1:ℝ) < n := by exact_mod_cast (by omega : 1 < n)
    nlinarith
  field_simp

end FinitePopulation
end GeometricMedianCoresets
