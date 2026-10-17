import Paper08.Algorithm

/-! # Magnitudes and numerator lengths of the actual rational recurrence -/

open scoped BigOperators

namespace Paper08.Moments

/-- A coarse uniform magnitude bound for every coefficient returned by the
rational program. The moment bound is an input bound, not an output certificate. -/
theorem rationalLogCoeff_abs_le (M : ℕ → ℚ) (B : ℚ) (s j : ℕ)
    (hB : 1 ≤ B) (hj : j ≤ s)
    (hM : ∀ k, 1 ≤ k → k ≤ s → |M k| ≤ B) :
    |rationalLogCoeff M j| ≤ (((s + 1 : ℕ) : ℚ) * B) ^ j := by
  let A : ℚ := ((s + 1 : ℕ) : ℚ) * B
  have hA : 1 ≤ A := by
    have hs : (1 : ℚ) ≤ ((s + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le s)
    dsimp [A]
    nlinarith
  change |rationalLogCoeff M j| ≤ A ^ j
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj0 : j = 0
    · subst j
      simp
    have hjp : 1 ≤ j := by omega
    have hjq : (0 : ℚ) < j := by exact_mod_cast hjp
    have hp : (1 : ℚ) ≤ A ^ (j - 1) := one_le_pow₀ hA
    have hterms : ∀ i ∈ Finset.range j,
        |(i : ℚ) * rationalLogCoeff M i * M (j - i)| ≤
          (j : ℚ) * A ^ (j - 1) * B := by
      intro i hi
      have hij := Finset.mem_range.mp hi
      have hji : 1 ≤ j - i := by omega
      have hd := ih i hij (by omega)
      have hdp : A ^ i ≤ A ^ (j - 1) := pow_le_pow_right₀ hA (by omega)
      have hiq : (i : ℚ) ≤ j := by exact_mod_cast (by omega : i ≤ j)
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg i)]
      exact mul_le_mul
        (mul_le_mul hiq (hd.trans hdp) (abs_nonneg _) hjq.le)
        (hM (j - i) hji (by omega)) (abs_nonneg _) (by positivity)
    have hsum : |∑ i ∈ Finset.range j, (i : ℚ) * rationalLogCoeff M i * M (j - i)| ≤
        (j : ℚ) * ((j : ℚ) * A ^ (j - 1) * B) := by
      calc
        _ ≤ ∑ i ∈ Finset.range j, |(i : ℚ) * rationalLogCoeff M i * M (j - i)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _i ∈ Finset.range j, (j : ℚ) * A ^ (j - 1) * B :=
          Finset.sum_le_sum hterms
        _ = _ := by simp [nsmul_eq_mul]
    rw [rationalLogCoeff_eq M hjp]
    have habs := _root_.abs_add_le (M j)
      (-((1 / (j : ℚ)) * ∑ i ∈ Finset.range j, (i : ℚ) * rationalLogCoeff M i * M (j - i)))
    rw [← sub_eq_add_neg, abs_neg] at habs
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℚ) < 1 / j)] at habs
    have hs := mul_le_mul_of_nonneg_left hsum (by positivity : (0 : ℚ) ≤ 1 / j)
    have hs' : (1 / (j : ℚ)) *
        |∑ i ∈ Finset.range j, (i : ℚ) * rationalLogCoeff M i * M (j - i)| ≤
          (j : ℚ) * A ^ (j - 1) * B := by
      convert hs using 1 <;> field_simp <;> ring
    have hjs : (j : ℚ) + 1 ≤ ((s + 1 : ℕ) : ℚ) := by exact_mod_cast Nat.succ_le_succ hj
    have hfinal : B + (j : ℚ) * A ^ (j - 1) * B ≤ A ^ j := by
      have hBp : B ≤ A ^ (j - 1) * B := by nlinarith
      have hAB : ((j : ℚ) + 1) * B ≤ A := by dsimp [A]; nlinarith
      have hm := mul_le_mul_of_nonneg_right hAB (pow_nonneg (by linarith : (0 : ℚ) ≤ A) (j - 1))
      have he : A ^ j = A * A ^ (j - 1) := by
        conv_lhs => rw [show j = (j - 1) + 1 by omega, pow_succ]
        ring
      rw [he]
      nlinarith
    exact (le_trans habs (add_le_add (hM j hjp hj) hs')).trans hfinal

/-- The numerator magnitude is exactly `|q|` times its canonical positive
denominator, as an equality in the rational numbers. -/
theorem rational_num_natAbs (q : ℚ) :
    (q.num.natAbs : ℚ) = |q| * (q.den : ℚ) := by
  have hd : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hn : (q.num : ℚ) = q * (q.den : ℚ) := (div_eq_iff hd).mp q.num_div_den
  calc
    (q.num.natAbs : ℚ) = |(q.num : ℚ)| := by simp only [Nat.cast_natAbs, Int.cast_abs]
    _ = |q| * |(q.den : ℚ)| := by rw [hn, abs_mul]
    _ = |q| * (q.den : ℚ) := by congr 1; exact abs_of_nonneg (Nat.cast_nonneg q.den)

/-- Concrete binary-size conversion for any reduced rational. -/
theorem rational_num_size_le_of_abs_den_le (q : ℚ) (U V : ℕ)
    (habs : |q| ≤ (2 : ℚ) ^ U) (hden : q.den ≤ 2 ^ V) :
    q.num.natAbs.size ≤ U + V + 1 := by
  have hn : (q.num.natAbs : ℚ) ≤ (2 : ℚ) ^ (U + V) := by
    rw [rational_num_natAbs, pow_add]
    exact mul_le_mul habs (by exact_mod_cast hden) (by positivity) (by positivity)
  have hn' : q.num.natAbs ≤ 2 ^ (U + V) := by exact_mod_cast hn
  apply Nat.size_le.mpr
  rw [pow_succ]
  have hp : 0 < (2 : ℕ) ^ (U + V) := by positivity
  omega

/-- When the computed moments are exponentially bounded, the actual output
coefficients have an explicit quadratic exponent bound. -/
theorem rationalLogCoeff_abs_le_two_pow (M : ℕ → ℚ) (a s : ℕ)
    (hM : ∀ k, 1 ≤ k → k ≤ s → |M k| ≤ (2 : ℚ) ^ (a * s))
    {j : ℕ} (hj : j ≤ s) :
    |rationalLogCoeff M j| ≤ (2 : ℚ) ^ ((a + 1) * s * s + s) := by
  have hB : (1 : ℚ) ≤ 2 ^ (a * s) := one_le_pow₀ (by norm_num)
  have h := rationalLogCoeff_abs_le M ((2 : ℚ) ^ (a * s)) s j hB hj hM
  have hs : ((s + 1 : ℕ) : ℚ) ≤ (2 : ℚ) ^ (s + 1) := by
    exact_mod_cast Nat.le_of_lt (s + 1).lt_two_pow_self
  have hbase : ((s + 1 : ℕ) : ℚ) * (2 : ℚ) ^ (a * s) ≤
      (2 : ℚ) ^ ((a + 1) * s + 1) := by
    have hm := mul_le_mul_of_nonneg_right hs (by positivity : (0 : ℚ) ≤ 2 ^ (a * s))
    convert hm using 1 <;> rw [← pow_add] <;> congr 1 <;> ring
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℚ) ≤ ((s + 1 : ℕ) : ℚ) * 2 ^ (a * s)) hbase j
  have he : ((2 : ℚ) ^ ((a + 1) * s + 1)) ^ j =
      (2 : ℚ) ^ (((a + 1) * s + 1) * j) := (pow_mul _ _ _).symm
  rw [he] at hp
  have hexp : ((a + 1) * s + 1) * j ≤ (a + 1) * s * s + s := by
    simpa only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc] using
      Nat.mul_le_mul_left ((a + 1) * s + 1) hj
  exact h.trans (hp.trans (pow_le_pow_right₀ (by norm_num) hexp))

/-- The numerator part of the polynomial bit bound (4.5), for the actual
recurrence program and canonical numerator representation. -/
theorem rationalLogCoeff_num_size_le (M : ℕ → ℚ) (P s r J a : ℕ)
    (hden : ∀ i, 1 ≤ i → i ≤ s → (M i).den ∣ denomBound P s r J)
    (habs : ∀ i, 1 ≤ i → i ≤ s → |M i| ≤ (2 : ℚ) ^ (a * s))
    {j : ℕ} (hj : j ≤ s) :
    (rationalLogCoeff M j).num.natAbs.size ≤
      ((a + 1) * s * s + s) + ((P * s + r * J) * s + s ^ 3 + s ^ 2) + 1 := by
  apply rational_num_size_le_of_abs_den_le
    (rationalLogCoeff M j) ((a + 1) * s * s + s)
    ((P * s + r * J) * s + s ^ 3 + s ^ 2)
    (rationalLogCoeff_abs_le_two_pow M a s habs hj)
  have hd := rationalLogCoeff_common_denominator M (denomBound P s r J) s
    (denomBound_pos P s r J) hden hj
  have hp : 0 < coefficientDenominator (denomBound P s r J) s := by
    unfold coefficientDenominator
    exact Nat.mul_pos (pow_pos (by have := denomBound_pos P s r J; omega) _) (Nat.factorial_pos _)
  exact (Nat.le_of_dvd hp hd).trans (common_denominator_le_two_pow P s r J)

end Paper08.Moments
