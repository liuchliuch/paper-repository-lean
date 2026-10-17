import Paper02.Basic
import Paper02.RudinShapiro
import Paper02.LSym
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

/-!
# Algebraic cores of Proposition 3.1, Corollary 3.2, Proposition 3.3
-/

noncomputable section

namespace Paper02.Bounds

open Paper02 Paper02.LSym Paper02.RS Real

lemma abs_add_le (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  have h : (|a + b|) ^ 2 ≤ (|a| + |b|) ^ 2 := by
    simp only [sq_abs, add_sq]
    have hab : a * b ≤ |a * b| := le_abs_self _
    have habs : |a * b| = |a| * |b| := abs_mul a b
    nlinarith [abs_mul_abs_self a, abs_mul_abs_self b, hab, habs]
  exact le_of_sq_le_sq h (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- If `|e(j)| ≤ 3η` on the three consecutive integers `k-1,k,k+1`,
then `|D e(k)| ≤ 6η`. -/
lemma secondDiff_error_le (e : ℤ → ℝ) (k : ℤ) (η : ℝ)
    (h1 : |e (k + 1)| ≤ 3 * η) (h2 : |e k| ≤ 3 * η) (h3 : |e (k - 1)| ≤ 3 * η) :
    |secondDiff e k| ≤ 6 * η := by
  rw [secondDiff_eq, abs_div, abs_two]
  have htri : |e (k + 1) - 2 * e k + e (k - 1)|
      ≤ |e (k + 1)| + |2 * e k| + |e (k - 1)| := by
    have d : e (k + 1) - 2 * e k + e (k - 1)
        = e (k + 1) + (-(2 * e k)) + e (k - 1) := by ring
    rw [d]
    have a := abs_add_le (e (k + 1) + (-(2 * e k))) (e (k - 1))
    have b := abs_add_le (e (k + 1)) (-(2 * e k))
    have c : |-(2 * e k)| = |2 * e k| := abs_neg _
    nlinarith [abs_nonneg (e (k + 1)), abs_nonneg (e k), abs_nonneg (e (k - 1))]
  have h2' : |2 * e k| = 2 * |e k| := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  have h4 : |e (k + 1)| + |2 * e k| + |e (k - 1)| ≤ 12 * η := by
    rw [h2']
    nlinarith
  have h5 : |e (k + 1) - 2 * e k + e (k - 1)| ≤ 12 * η := le_trans htri h4
  have h6 : |e (k + 1) - 2 * e k + e (k - 1)| / 2 ≤ 6 * η := by
    nlinarith [abs_nonneg (e (k + 1) - 2 * e k + e (k - 1))]
  nlinarith [abs_nonneg ((e (k + 1) - 2 * e k + e (k - 1)) / (2:ℝ))]

/-- **Proposition 3.1 (algebraic core).** -/
lemma prop_3_1_algebra (N : ℕ) (η ρ s1 : ℝ)
    (hN : 16 ≤ N) (hη' : η < 1/6)
    (hpair : (1 - 6 * η) * ((N:ℝ) - 3) ≤ s1 * (Real.sqrt (2 * (N:ℝ)) + 3))
    (hs1 : s1 ≤ 3 * ρ) :
    (1 - 6 * η) * ((N:ℝ) - 3) / (3 * (Real.sqrt (2 * (N:ℝ)) + 3)) ≤ ρ := by
  have hden : 0 < 3 * (Real.sqrt (2 * (N:ℝ)) + 3) := by
    have h2N : (0:ℝ) < 2 * N := by
      have : (0:ℝ) < N := by
        have : (0:ℕ) < N := lt_of_lt_of_le (by norm_num) hN
        exact_mod_cast this
      positivity
    have hsq' : 0 < Real.sqrt (2 * (N:ℝ)) + 3 := by
      nlinarith [Real.sqrt_nonneg (2 * (N:ℝ))]
    positivity
  have hN3 : (0:ℝ) ≤ N - 3 := by
    have : (3:ℝ) ≤ N := by
      have : (3:ℕ) ≤ N := by omega
      exact_mod_cast this
    linarith
  have hpos : 0 ≤ 1 - 6 * η := by nlinarith
  have hs1b : (1 - 6 * η) * ((N:ℝ) - 3) ≤ 3 * ρ * (Real.sqrt (2 * (N:ℝ)) + 3) := by
    have hmul := mul_le_mul_of_nonneg_right hs1
      (by nlinarith [Real.sqrt_nonneg (2 * (N:ℝ))] : 0 ≤ Real.sqrt (2 * (N:ℝ)) + 3)
    nlinarith
  rw [div_le_iff₀ hden]
  nlinarith

/-- At `η = 1/100`, `47(N-3)/150 ≥ N/6` for `N ≥ 16`. -/
lemma eta_inv100_first (N : ℕ) (hN : 16 ≤ N) :
    (N:ℝ) * 150 ≤ 47 * ((N:ℝ) - 3) * 6 := by
  have hNle : (16:ℝ) ≤ N := by
    have : (16:ℕ) ≤ N := hN
    exact_mod_cast this
  nlinarith

/-- For `N ≥ 16`, `3 ≤ √(2N)`. -/
lemma three_le_sqrt_twoN (N : ℕ) (hN : 16 ≤ N) :
    (3:ℝ) ≤ Real.sqrt (2 * (N:ℝ)) := by
  have hNle : (16:ℝ) ≤ N := by
    have : (16:ℕ) ≤ N := hN
    exact_mod_cast this
  have h18 : (18:ℝ) ≤ 2 * N := by nlinarith
  have hsq : Real.sqrt 18 ≤ Real.sqrt (2 * (N:ℝ)) := Real.sqrt_le_sqrt h18
  have h18eq : Real.sqrt (18:ℝ) = 3 * Real.sqrt 2 := by
    have h9 : Real.sqrt (9:ℝ) = 3 := by norm_num
    have h : Real.sqrt (18:ℝ) = Real.sqrt (9 * 2) := by norm_num
    rw [h, Real.sqrt_mul (by norm_num : 0 ≤ (9:ℝ)), h9]
  rw [h18eq] at hsq
  have hsplit : Real.sqrt (2 * (N:ℝ)) = Real.sqrt 2 * Real.sqrt (N:ℝ) := by
    rw [Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ))]
  have hN0 : (0:ℝ) ≤ N := by nlinarith
  nlinarith [hsplit, Real.sqrt_nonneg 2, Real.sqrt_nonneg (N:ℝ),
    Real.mul_self_sqrt hN0, Real.mul_self_sqrt (by norm_num : 0 ≤ (2:ℝ))]

/-- **Corollary 3.2 (root comparison).** -/
lemma cor_3_2_sqrt (n N : ℕ) (hgt : (n:ℝ) + 1 < 2 * N) :
    Real.sqrt ((n:ℝ) + 1) < Real.sqrt 2 * Real.sqrt (N:ℝ) := by
  have hnpos : 0 ≤ (n:ℝ) + 1 := by
    have : (0:ℝ) ≤ n := by
      have : (0:ℕ) ≤ n := by omega
      exact_mod_cast this
    linarith
  have h : (n:ℝ) + 1 < 2 * N := hgt
  have hlt : Real.sqrt ((n:ℝ) + 1) < Real.sqrt (2 * (N:ℝ)) := by
    exact Real.sqrt_lt_sqrt (by nlinarith) h
  rw [Real.sqrt_mul (by norm_num : 0 ≤ (2:ℝ))] at hlt
  nlinarith [Real.sqrt_nonneg 2]

/-- **Proposition 3.3 (Cauchy–Schwarz).** -/
lemma prop_3_3_cs (p : ℕ) (c : Fin p → ℝ) (hp : 0 < p) :
    (∑ j, |c j|) ≤ Real.sqrt (p:ℝ) * Real.sqrt (∑ j, |c j| ^ 2) := by
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin p))
    (fun _ : Fin p => (1:ℝ)) (fun j => |c j|)
  have h1 : (∑ j, (1:ℝ) * |c j|) ^ 2
      ≤ (∑ j, (1:ℝ) ^ 2) * (∑ j, |c j| ^ 2) := hcs
  simp only [one_mul, one_pow] at h1
  have hsum1 : (∑ j : Fin p, (1:ℝ)) = p := by
    have hcard : (Finset.univ : Finset (Fin p)).card = p := Fintype.card_fin p
    rw [Finset.sum_const, hcard]
    simp
  rw [hsum1] at h1
  have h3 : 0 ≤ ∑ j, |c j| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have h4 : 0 ≤ ∑ j, |c j| ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h8 : Real.sqrt ((∑ j, |c j|) ^ 2) = ∑ j, |c j| := Real.sqrt_sq h3
  have h9 : Real.sqrt ((p:ℝ) * ∑ j, |c j| ^ 2)
      = Real.sqrt (p:ℝ) * Real.sqrt (∑ j, |c j| ^ 2) := by
    have hppos : (0:ℝ) ≤ p := by
      have : (0:ℝ) < p := by exact_mod_cast hp
      exact le_of_lt this
    rw [Real.sqrt_mul hppos]
  have := Real.sqrt_le_sqrt h1
  rw [h8, h9] at this
  exact this

/-- **Proposition 3.3 (Parseval + Cauchy–Schwarz).**
If `∑ |c_j|² ≤ 9` then `∑ |c_j| ≤ 3√p`. -/
lemma prop_3_3_bound (p : ℕ) (c : Fin p → ℝ) (hp : 0 < p)
    (h : ∑ j, |c j| ^ 2 ≤ 9) :
    (∑ j, |c j|) ≤ 3 * Real.sqrt (p:ℝ) := by
  have h1 := prop_3_3_cs p c hp
  have h3 : Real.sqrt (∑ j, |c j| ^ 2) ≤ 3 := by
    have := Real.sqrt_le_sqrt h
    have h9 : Real.sqrt (9:ℝ) = 3 := by norm_num
    rw [h9] at this
    exact this
  have hspp : 0 ≤ Real.sqrt (p:ℝ) := Real.sqrt_nonneg _
  have hsp : 0 ≤ Real.sqrt (∑ j, |c j| ^ 2) := Real.sqrt_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h3 hspp]

end Paper02.Bounds
