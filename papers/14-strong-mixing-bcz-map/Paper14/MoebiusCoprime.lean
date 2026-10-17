import Paper14.WeakMixing

open MeasureTheory Filter Topology Set
namespace Paper14

/-- The actual Möbius coprimality identity used in Appendix A. -/
theorem moebiusCoprimeIdentity : MoebiusCoprimeIdentity := by
  intro p q hp hq
  have hg : Nat.gcd p q ≠ 0 := (Nat.gcd_pos_of_pos_left q hp).ne'
  have hdiv : (Nat.gcd p q).divisors = p.divisors ∩ q.divisors := by
    ext d
    simp [Nat.mem_divisors,hg,hp.ne',hq.ne',Nat.dvd_gcd_iff]
  have hsum : (∑ d ∈ (Nat.gcd p q).divisors, (ArithmeticFunction.moebius d : ℤ)) =
      if Nat.gcd p q = 1 then (1 : ℤ) else 0 := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply,
      ArithmeticFunction.moebius_mul_coe_zeta,ArithmeticFunction.one_apply]
  rw [← hdiv]
  have hcast := congrArg (fun z : ℤ => (z : ℝ)) hsum
  push_cast at hcast
  by_cases hcop : Nat.Coprime p q
  · have hg1 : Nat.gcd p q = 1 := hcop.gcd_eq_one
    simpa only [if_pos hcop,if_pos hg1] using hcast.symm
  · have hg1 : Nat.gcd p q ≠ 1 := fun h => hcop (by exact h)
    simpa only [if_neg hcop,if_neg hg1] using hcast.symm

end Paper14
