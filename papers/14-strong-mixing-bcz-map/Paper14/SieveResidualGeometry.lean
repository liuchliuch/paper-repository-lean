import Paper14.SieveActualMoments
import Mathlib.RingTheory.Int.Basic

open MeasureTheory Set Finset Function
namespace Paper14
noncomputable section

/-- The zero modulus imposes exactly full primitivity, so the corrected
original primitive count has the same finite single-q expansion. -/
lemma GPrim_eq_GM_zero (Q : ℕ) (c θ ε : ℝ) : GPrim Q c θ ε = GM 0 Q c θ ε := by
  unfold GPrim GM
  congr 1
  ext pq
  simp only [mem_setOf_eq,Int.ofNat_eq_coe,Nat.cast_zero,Int.gcd_zero_right,
    Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast]

/-- A nonprimitive point that survives the finite prime sieve has a common
prime divisor larger than P, with no additional arithmetic certificate. -/
lemma surviving_nonprimitive_large_prime (P : ℕ) {p : ℤ} {q : ℕ}
    (hfinite : IsCoprime p ((Int.gcd (q : ℤ) (primorial P : ℤ) : ℕ) : ℤ))
    (hprim : ¬ IsCoprime p (q : ℤ)) :
    ∃ ℓ : ℕ, Nat.Prime ℓ ∧ P < ℓ ∧ ℓ ∣ q ∧ (ℓ : ℤ) ∣ p := by
  have hg : Nat.gcd p.natAbs q ≠ 1 := by
    intro heq
    apply hprim
    rw [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast]
    exact heq
  obtain ⟨ℓ,hℓ,hℓg⟩ := Nat.exists_prime_and_dvd hg
  have hℓp : (ℓ : ℤ) ∣ p := Int.natCast_dvd.mpr (hℓg.trans (Nat.gcd_dvd_left _ _))
  have hℓq : ℓ ∣ q := hℓg.trans (Nat.gcd_dvd_right _ _)
  refine ⟨ℓ,hℓ,?_,hℓq,hℓp⟩
  by_contra hn
  have hℓP : ℓ ≤ P := by omega
  have hℓM : ℓ ∣ primorial P := by
    unfold primorial
    exact Finset.dvd_prod_of_mem _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),hℓ⟩)
  have hℓd : (ℓ : ℤ) ∣ ((Int.gcd (q : ℤ) (primorial P : ℤ) : ℕ) : ℤ) := by
    rw [Int.gcd_natCast_natCast,Int.natCast_dvd_natCast]
    exact Nat.dvd_gcd hℓq hℓM
  have hunit := hfinite.isUnit_of_dvd' hℓp hℓd
  obtain h1 | hneg := Int.isUnit_iff.mp hunit
  · have : ℓ = 1 := by exact_mod_cast h1
    exact hℓ.ne_one this
  · have hnn : (0 : ℤ) ≤ ℓ := Int.natCast_nonneg _
    omega

lemma GM_cast_sum_nat (M Q : ℕ) (c θ ε : ℝ) (hε : ε ≤ 1) :
    (GM M Q c θ ε : ℝ) = ∑ q ∈ Finset.range Q,
      (sieveSingle M ((q+1 : ℕ) : ℤ) ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) := by
  rw [← sieveTorusCount_real_eq_GM M Q ε θ c hε]
  simp only [sieveTorusCount,Finset.sum_apply,sieveTorusSingle,sieve_indicator_real_representatives,
    Int.cast_natCast]

lemma GPrim_cast_sum_nat (Q : ℕ) (c θ ε : ℝ) (hε : ε ≤ 1) :
    (GPrim Q c θ ε : ℝ) = ∑ q ∈ Finset.range Q,
      (sieveSingle 0 ((q+1 : ℕ) : ℤ) ε (((q+1 : ℕ) : ℝ)*θ-c) : ℝ) := by
  rw [GPrim_eq_GM_zero]
  exact GM_cast_sum_nat 0 Q c θ ε hε

end
end Paper14
