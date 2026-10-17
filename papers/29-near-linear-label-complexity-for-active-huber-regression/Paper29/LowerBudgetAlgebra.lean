import Paper29.HardDistribution
import Paper29.QueryModel

noncomputable section
open scoped BigOperators
namespace Paper29.HardDistribution

/-- Exact reciprocal-max identity used in (4.11), with no asymptotic notation. -/
theorem beta_inverse_identity (r N : ℕ) {ε : ℝ} (hε : 0 < ε) (hN : 0 < N) :
    (r:ℝ)/(beta ε N)^2 = min ((r:ℝ)/(40000*ε^2)) ((r:ℝ)*N/10) := by
  have hNR : (0:ℝ) < N := by exact_mod_cast hN
  have hroot : Real.sqrt (10/(N:ℝ))^2 = 10/(N:ℝ) := Real.sq_sqrt (by positivity)
  have hroot0 := Real.sqrt_nonneg (10/(N:ℝ))
  have hr : (0:ℝ) ≤ r := Nat.cast_nonneg r
  by_cases hh : Real.sqrt (10/(N:ℝ)) ≤ 200*ε
  · rw [beta, max_eq_left hh]
    have hs : 10/(N:ℝ) ≤ 40000*ε^2 := by nlinarith
    have hleft : (r:ℝ)/(40000*ε^2) ≤ (r:ℝ)*N/10 := by
      apply (div_le_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hε))).2
      have he := (div_le_iff₀ hNR).1 hs
      nlinarith [mul_nonneg hr (show 0 ≤ (40000*ε^2)*(N:ℝ)-10 by linarith)]
    rw [min_eq_left hleft]
    congr 1
    ring
  · have hle : 200*ε ≤ Real.sqrt (10/(N:ℝ)) := (lt_of_not_ge hh).le
    rw [beta, max_eq_right hle, hroot]
    have hright : (r:ℝ)*N/10 ≤ (r:ℝ)/(40000*ε^2) := by
      apply (le_div_iff₀ (mul_pos (by norm_num) (sq_pos_of_pos hε))).2
      have hs : 40000*ε^2 ≤ 10/(N:ℝ) := by nlinarith
      have he := (le_div_iff₀ hNR).1 hs
      nlinarith [mul_nonneg hr (show 0 ≤ 10-(40000*ε^2)*(N:ℝ) by linarith)]
    rw [min_eq_right hright]
    field_simp

/-- Floor bookkeeping for all admissible pool sizes in the long-block regime. -/
theorem long_block_mass (n r : ℕ) (hr : 1 ≤ r) (hN : 160 ≤ n/r) :
    (159/160:ℝ)*n ≤ (r:ℝ)*((n/r:ℕ):ℝ) := by
  have hr0 : 0 < r := by omega
  have hdiv := Nat.div_add_mod n r
  have hmod := Nat.mod_lt n hr0
  have hm : 160*r ≤ r*(n/r) := by nlinarith
  have hdivR : (r:ℝ)*((n/r:ℕ):ℝ)+(n%r:ℕ) = n := by exact_mod_cast hdiv
  have hmodR : ((n%r:ℕ):ℝ) < r := by exact_mod_cast hmod
  have hmR : (160:ℝ)*r ≤ (r:ℝ)*((n/r:ℕ):ℝ) := by exact_mod_cast hm
  nlinarith [(Nat.cast_nonneg (n%r) : (0:ℝ) ≤ (n%r:ℕ))]

/-- Uniform numerical lower-budget consequence of the exact hard parameter. -/
theorem long_inverse_budget (n r : ℕ) (hr : 1 ≤ r) (hN : 160 ≤ n/r)
    {ε : ℝ} (hε : 0 < ε) :
    (1/40000:ℝ)*min (n:ℝ) ((r:ℝ)/ε^2) ≤ (r:ℝ)/(beta ε (n/r))^2 := by
  rw [beta_inverse_identity r (n/r) hε (by omega)]
  have hm := long_block_mass n r hr hN
  apply le_min
  · have hh := mul_le_mul_of_nonneg_left (min_le_right (n:ℝ) ((r:ℝ)/ε^2))
      (by norm_num : (0:ℝ)≤1/40000)
    convert hh using 1 <;> ring
  · have hh := mul_le_mul_of_nonneg_left (min_le_left (n:ℝ) ((r:ℝ)/ε^2))
      (by norm_num : (0:ℝ)≤1/40000)
    have hn : (0:ℝ) ≤ n := Nat.cast_nonneg n
    nlinarith

end Paper29.HardDistribution
