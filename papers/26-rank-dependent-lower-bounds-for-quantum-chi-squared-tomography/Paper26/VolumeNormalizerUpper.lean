import Paper26.VolumeRates

/-! The remaining elementary upper bound on the exact factorial-product
normalizer in Lemma 2.1. -/
noncomputable section
open scoped BigOperators

namespace Paper26.VolumeNormalizerUpper

theorem factorial_le_ascFactorial (j s : ℕ) : s.factorial ≤ (j + 1).ascFactorial s := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.factorial_succ, Nat.ascFactorial_succ]
    exact Nat.mul_le_mul (by omega) ih

theorem factorial_ratio_upper (s j : ℕ) :
    (j.factorial : ℝ) / ((s + j).factorial : ℝ) ≤ 1 / (s.factorial : ℝ) := by
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast Nat.factorial_pos s
  have hasc : (s.factorial : ℝ) ≤ ((j + 1).ascFactorial s : ℝ) := by
    exact_mod_cast factorial_le_ascFactorial j s
  have he : ((s + j).factorial : ℝ) =
      (j.factorial : ℝ) * ((j + 1).ascFactorial s : ℝ) := by
    rw [Nat.add_comm s j]
    exact_mod_cast (Nat.factorial_mul_ascFactorial j s).symm
  have hj : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  calc
    _ = 1 / ((j + 1).ascFactorial s : ℝ) := by rw [he]; field_simp
    _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hfac hasc

theorem graphNormalizer_upper (s r : ℕ) (hs : 0 < s) :
    VolumeRates.graphNormalizer s r ≤ (Real.pi * Real.exp 1 / (s : ℝ)) ^ (r * s) := by
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hprod : (∏ j ∈ Finset.range r, (j.factorial : ℝ) / ((s + j).factorial : ℝ)) ≤
      (1 / (s.factorial : ℝ)) ^ r := by
    simpa only [Finset.prod_const, Finset.card_range] using
      (Finset.prod_le_prod (fun j (_ : j ∈ Finset.range r) => by positivity)
        (fun j _ => factorial_ratio_upper s j))
  have hfac : 1 / (s.factorial : ℝ) ≤ (Real.exp 1 / (s : ℝ)) ^ s := by
    calc
      _ ≤ 1 / (((s : ℝ) / Real.exp 1) ^ s) :=
        div_le_div_of_nonneg_left (by norm_num) (by positivity)
          (VolumeRates.pow_div_exp_le_factorial s hs)
      _ = _ := by rw [← one_div_pow]; congr 1; field_simp
  calc
    VolumeRates.graphNormalizer s r ≤ Real.pi ^ (r * s) * (1 / (s.factorial : ℝ)) ^ r :=
      mul_le_mul_of_nonneg_left hprod (by positivity)
    _ ≤ Real.pi ^ (r * s) * ((Real.exp 1 / (s : ℝ)) ^ s) ^ r :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hfac r) (by positivity)
    _ = (Real.pi * Real.exp 1 / (s : ℝ)) ^ (r * s) := by
      rw [← pow_mul, Nat.mul_comm s r, ← mul_pow]
      congr 1
      ring

end Paper26.VolumeNormalizerUpper
