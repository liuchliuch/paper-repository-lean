import Paper29.SamplingSizes
import Paper29.QueryModel

noncomputable section
open scoped BigOperators
namespace Paper29.ProcessTools

theorem upperBudget_mono_constant {n r : ℕ} {C D ε : ℝ} (hCD : C ≤ D) :
    QueryModel.upperBudget n r C ε ≤ QueryModel.upperBudget n r D ε := by
  apply min_le_min_left
  have hf : 0 ≤ Real.log (2*(n:ℝ))^6+Real.log (2*(n:ℝ))^4/ε^2 := by positivity
  have hh := mul_le_mul_of_nonneg_right hCD (mul_nonneg (Nat.cast_nonneg r) hf)
  convert hh using 1 <;> ring

theorem upperBudget_mono_pool {N n r : ℕ} (hN : 1 ≤ N) (hNn : N ≤ n)
    {C ε : ℝ} (hC : 0 ≤ C) : QueryModel.upperBudget N r C ε ≤ QueryModel.upperBudget n r C ε := by
  have hNR : (1:ℝ) ≤ N := by exact_mod_cast hN
  have hNnR : (N:ℝ) ≤ n := by exact_mod_cast hNn
  have hlog : 0 ≤ Real.log (2*(N:ℝ)) := (Real.log_pos (by linarith : (1:ℝ)<2*N)).le
  have hlogs : Real.log (2*(N:ℝ)) ≤ Real.log (2*(n:ℝ)) :=
    Real.log_le_log (by linarith) (by linarith)
  apply min_le_min hNnR
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC (Nat.cast_nonneg r))
  apply add_le_add (pow_le_pow_left₀ hlog hlogs 6)
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ hlog hlogs 4) (sq_nonneg ε)

theorem small_pool_budget {n r : ℕ} (hn : 1 ≤ n) (hn16 : n ≤ 16) (hr : 1 ≤ r)
    {C ε : ℝ} (hC : 16/(Real.log 2)^6 ≤ C) : (n:ℝ) ≤ QueryModel.upperBudget n r C ε := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn16R : (n:ℝ) ≤ 16 := by exact_mod_cast hn16
  have hrR : (1:ℝ) ≤ r := by exact_mod_cast hr
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hln : Real.log 2 ≤ Real.log (2*(n:ℝ)) := Real.log_le_log (by norm_num) (by linarith)
  have hln0 : 0 ≤ Real.log (2*(n:ℝ)) := hl2.le.trans hln
  have hpw := pow_le_pow_left₀ hl2.le hln 6
  have hC0 : 0 ≤ C := (div_nonneg (by norm_num) (pow_nonneg hl2.le 6)).trans hC
  have hCr : C ≤ C*r := le_mul_of_one_le_right hC0 hrR
  have hT : 16 ≤ C*r*Real.log (2*(n:ℝ))^6 := by
    have hc : 16 ≤ C*(Real.log 2)^6 := (div_le_iff₀ (pow_pos hl2 6)).1 hC
    exact hc.trans ((mul_le_mul_of_nonneg_right hCr (pow_nonneg hl2.le 6)).trans
      (mul_le_mul_of_nonneg_left hpw (mul_nonneg hC0 (Nat.cast_nonneg r))))
  apply le_min le_rfl
  have ht := mul_nonneg (mul_nonneg hC0 (Nat.cast_nonneg r))
    (div_nonneg (pow_nonneg hln0 4) (sq_nonneg ε))
  nlinarith

end Paper29.ProcessTools
