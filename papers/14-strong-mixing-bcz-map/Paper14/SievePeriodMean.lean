import Paper14.PeriodicSums
import Paper14.MoebiusCoprime
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Primorial

open Finset Function Filter Topology
namespace Paper14
noncomputable section

def reciprocalAF : ArithmeticFunction ℝ where
  toFun n := (n : ℝ)⁻¹
  map_zero' := by simp

lemma reciprocalAF_mult : reciprocalAF.IsMultiplicative := by
  constructor
  · simp [reciprocalAF]
  · intro m n hmn
    simp [reciprocalAF,Nat.cast_mul,mul_inv_rev,mul_comm]

def reciprocalSqAF : ArithmeticFunction ℝ where
  toFun n := (n : ℝ)⁻¹^2
  map_zero' := by simp

lemma reciprocalSqAF_mult : reciprocalSqAF.IsMultiplicative := by
  constructor
  · simp [reciprocalSqAF]
  · intro m n hmn
    simp [reciprocalSqAF,Nat.cast_mul,mul_inv_rev,mul_pow,mul_comm]

lemma varrho_eq_moebius_divisor_sum {M : ℕ} (hM : Squarefree M) (q : ℕ) :
    varrho M q = ∑ d ∈ (Nat.gcd q M).divisors,
      ((ArithmeticFunction.moebius d : ℤ) : ℝ)*(d : ℝ)⁻¹ := by
  have hg : Squarefree (Nat.gcd q M) := hM.squarefree_of_dvd (Nat.gcd_dvd_right q M)
  rw [varrho,← Finset.prod_filter,← Nat.primeFactors_eq_to_filter_divisors_prime]
  exact reciprocalAF_mult.prodPrimeFactors_one_sub_of_squarefree reciprocalAF hg

lemma varrho_eq_moebius_filter {M : ℕ} (hM : Squarefree M) (q : ℕ) :
    varrho M q = ∑ d ∈ M.divisors,
      if d ∣ q then ((ArithmeticFunction.moebius d : ℤ) : ℝ)*(d : ℝ)⁻¹ else 0 := by
  rw [varrho_eq_moebius_divisor_sum hM,
    ← Nat.divisors_filter_dvd_of_dvd hM.ne_zero (Nat.gcd_dvd_right q M),Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  have hdiv : d ∣ Nat.gcd q M ↔ d ∣ q := by
    rw [Nat.dvd_gcd_iff]
    exact and_iff_left (Nat.dvd_of_mem_divisors hd)
  simp only [hdiv]

/-- The exact finite-sieve period mean, proved by Möbius divisor expansion
and exact multiple counts. This is the arithmetic identity used by CRT
in the paper, for any squarefree modulus. -/
theorem varrho_period_mean {M : ℕ} (hM : Squarefree M) :
    (∑ q ∈ Finset.range M, varrho M (q+1))/(M : ℝ) =
      ∏ p ∈ M.primeFactors, (1-(p : ℝ)⁻¹^2) := by
  have hMr : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne_zero
  have hsum : (∑ q ∈ Finset.range M, varrho M (q+1)) =
      ∑ d ∈ M.divisors, ((M/d : ℕ) : ℝ)*(((ArithmeticFunction.moebius d : ℤ) : ℝ)*(d : ℝ)⁻¹) := by
    simp_rw [varrho_eq_moebius_filter hM]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro d hd
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,Nat.card_multiples]
  rw [hsum,Finset.sum_div]
  change _ = ∏ p ∈ M.primeFactors, (1-reciprocalSqAF p)
  rw [reciprocalSqAF_mult.prodPrimeFactors_one_sub_of_squarefree reciprocalSqAF hM]
  apply Finset.sum_congr rfl
  intro d hd
  have hdM : d ∣ M := Nat.dvd_of_mem_divisors hd
  have hdr : (d : ℝ) ≠ 0 := by
    exact_mod_cast (ne_zero_of_dvd_ne_zero hM.ne_zero hdM)
  rw [Nat.cast_div hdM hdr]
  change ((M : ℝ)/(d : ℝ))*(((ArithmeticFunction.moebius d : ℤ) : ℝ)*(d : ℝ)⁻¹)/(M : ℝ) =
    ((ArithmeticFunction.moebius d : ℤ) : ℝ)*(d : ℝ)⁻¹^2
  field_simp [hMr,hdr]

lemma squarefree_primorial (P : ℕ) : Squarefree (primorial P) := by
  unfold primorial
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hpp := (Finset.mem_filter.mp hp).2
    have hqp := (Finset.mem_filter.mp hq).2
    exact Nat.coprime_iff_isRelPrime.mp ((Nat.coprime_primes hpp hqp).mpr hpq)
  · intro p hp
    exact (Finset.mem_filter.mp hp).2.squarefree

lemma primeFactors_primorial (P : ℕ) : (primorial P).primeFactors = (P+1).primesBelow := by
  unfold primorial
  exact Nat.primeFactors_prod (fun p hp => (Finset.mem_filter.mp hp).2)

/-- The exact period mean (paper Ex39), for the actual finite prime
sieve modulus, proved by divisor expansion instead of treating CRT as an
unproved arithmetic certificate. -/
theorem varrho_primorial_period_mean (P : ℕ) :
    (∑ q ∈ Finset.range (primorial P), varrho (primorial P) (q+1))/(primorial P : ℝ) = deltaM P := by
  rw [varrho_period_mean (squarefree_primorial P),primeFactors_primorial,deltaM_eq_prod_primesBelow]
  apply Finset.prod_congr rfl
  intro p hp
  rw [inv_pow]

/-- Equation (17) with the original finite-sieve constant delta_M. -/
theorem betaN_limit (P : ℕ) {K : ℝ} (hK : 0 < K) (α : ℝ) :
    Tendsto (fun n : ℕ => betaN (primorial P) ⌊2*(n : ℝ)/K⌋₊ (α/(n : ℝ))) atTop
      (𝓝 ((2*α/K)*deltaM P)) := by
  simpa only [varrho_primorial_period_mean] using
    betaN_period_mean_limit (primorial_pos P) hK α

end
end Paper14
