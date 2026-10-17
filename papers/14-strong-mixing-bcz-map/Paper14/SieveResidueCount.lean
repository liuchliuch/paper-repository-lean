import Paper14.SieveIndicatorMean
import Paper14.SievePeriodMean
import Paper14.DivisorWindows
import Mathlib.RingTheory.Int.Basic

open Finset Function Filter Topology Set MeasureTheory
namespace Paper14
noncomputable section

lemma admissibleResidues_card_nat (M : ℕ) (q : ℤ) :
    (admissibleResidues M q).card =
      ((Finset.Ioc 0 M).filter (fun p => Nat.Coprime p (Int.gcd q M))).card := by
  classical
  apply Finset.card_bij (fun p _ => p.toNat)
  · intro p hp
    obtain ⟨hpI,hcop⟩ := Finset.mem_filter.mp hp
    obtain ⟨hp1,hpM⟩ := Finset.mem_Icc.mp hpI
    simp only [Int.ofNat_eq_coe] at hpM
    have hp0 : 0 ≤ p := by omega
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_Ioc.mpr
      exact ⟨by omega,Int.toNat_le.mpr hpM⟩
    · rw [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast] at hcop
      have hab : p.natAbs = p.toNat := by
        exact_mod_cast (Int.natAbs_of_nonneg hp0).trans (Int.toNat_of_nonneg hp0).symm
      simpa only [hab,Int.ofNat_eq_coe] using hcop
  · intro p hp p' hp' heq
    have hp0 : 0 ≤ p := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp).1).1; omega
    have hp0' : 0 ≤ p' := by have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hp').1).1; omega
    omega
  · intro p hp
    obtain ⟨hpI,hcop⟩ := Finset.mem_filter.mp hp
    refine ⟨(p : ℤ),?_,by simp⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp only [Int.ofNat_eq_coe]
      apply Finset.mem_Icc.mpr
      obtain ⟨hp0,hpM⟩ := Finset.mem_Ioc.mp hpI
      exact ⟨by exact_mod_cast hp0,by exact_mod_cast hpM⟩
    · simpa only [Int.isCoprime_iff_nat_coprime,Int.natAbs_natCast] using hcop

lemma coprime_residue_count_divisor_sum {M D : ℕ} (hM : 0 < M) (hD : D ∣ M) :
    (((Finset.Ioc 0 M).filter (fun p => Nat.Coprime p D)).card : ℝ) =
      ∑ d ∈ D.divisors, ((M/d : ℕ) : ℝ)*((ArithmeticFunction.moebius d : ℤ) : ℝ) := by
  classical
  have hD0 : 0 < D := Nat.pos_of_dvd_of_pos hD hM
  have hid (p : ℕ) (hp : p ∈ Finset.Ioc 0 M) :
      (if Nat.Coprime p D then (1 : ℝ) else 0) =
        ∑ d ∈ D.divisors, if d ∣ p then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
    rw [moebiusCoprimeIdentity p D (Finset.mem_Ioc.mp hp).1 hD0]
    have heq : p.divisors ∩ D.divisors = D.divisors.filter (fun d => d ∣ p) := by
      ext d
      simp only [Finset.mem_inter,Finset.mem_filter,Nat.mem_divisors]
      have hp0 := (Finset.mem_Ioc.mp hp).1.ne'
      tauto
    rw [heq,Finset.sum_filter]
  have hcount : (((Finset.Ioc 0 M).filter (fun p => Nat.Coprime p D)).card : ℝ) =
      ∑ p ∈ Finset.Ioc 0 M, if Nat.Coprime p D then (1 : ℝ) else 0 := by
    rw [← Finset.sum_filter]
    simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hcount]
  calc _ = ∑ p ∈ Finset.Ioc 0 M, ∑ d ∈ D.divisors,
        if d ∣ p then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 :=
      Finset.sum_congr rfl hid
       _ = ∑ d ∈ D.divisors, ∑ p ∈ Finset.Ioc 0 M,
        if d ∣ p then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := Finset.sum_comm
       _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.sum_filter,Finset.sum_const,Nat.Ioc_filter_dvd_card_eq_div,nsmul_eq_mul]

/-- The exact admissible residue cardinality used in the actual indicator
mean in (16). -/
theorem admissibleResidues_card {M : ℕ} (hM : Squarefree M) (q : ℕ) :
    ((admissibleResidues M (q : ℤ)).card : ℝ) = (M : ℝ)*varrho M q := by
  rw [admissibleResidues_card_nat,Int.gcd_natCast_natCast,
    coprime_residue_count_divisor_sum (Nat.pos_of_ne_zero hM.ne_zero) (Nat.gcd_dvd_right q M),
    varrho_eq_moebius_divisor_sum hM,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdM := (Nat.dvd_of_mem_divisors hd).trans (Nat.gcd_dvd_right q M)
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast ne_zero_of_dvd_ne_zero hM.ne_zero hdM
  rw [Nat.cast_div hdM hdr]
  ring

/-- The real-period mean of each actual sieve indicator is exactly its
Euler-factor probability. -/
theorem integral_sieveSingle_period_eq {M : ℕ} (hM : Squarefree M) (q : ℕ)
    {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    (∫ u in Ioc (0 : ℝ) (M : ℝ), (sieveSingle M (q : ℤ) ε u : ℝ)) =
      (M : ℝ)*(ε*varrho M q) := by
  rw [integral_sieveSingle_period M (q : ℤ) hε0 hε1,admissibleResidues_card hM]
  ring

end
end Paper14
