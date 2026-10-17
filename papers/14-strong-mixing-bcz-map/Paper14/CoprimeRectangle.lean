import Paper14.MoebiusCoprime
import Paper14.DivisorWindows
import Mathlib.Analysis.Normed.Group.Tannery

open Finset Filter Topology
namespace Paper14
noncomputable section

/-- Exact Möbius expansion of a positive integer rectangle. -/
theorem coprime_rectangle_moebius (A B : Finset ℕ) (N : ℕ)
    (hA : ∀ p ∈ A, 0 < p) (hB : ∀ q ∈ B, 0 < q)
    (hN : ∀ p ∈ A, p ≤ N) :
    (((A ×ˢ B).filter (fun pq => Nat.Coprime pq.1 pq.2)).card : ℝ) =
      ∑ d ∈ Finset.range (N+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)*
        ((A.filter (fun p => d ∣ p)).card : ℝ)*((B.filter (fun q => d ∣ q)).card : ℝ) := by
  classical
  have hid (p : ℕ) (hp : p ∈ A) (q : ℕ) (hq : q ∈ B) :
      (if Nat.Coprime p q then (1 : ℝ) else 0) =
        ∑ d ∈ Finset.range (N+1), if d ∣ p ∧ d ∣ q then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
    rw [moebiusCoprimeIdentity p q (hA p hp) (hB q hq)]
    have hdiv : p.divisors ∩ q.divisors =
        (Finset.range (N+1)).filter (fun d => d ∣ p ∧ d ∣ q) := by
      ext d
      simp only [Finset.mem_inter,Nat.mem_divisors,Finset.mem_filter,Finset.mem_range]
      constructor
      · rintro ⟨⟨hdp,_⟩,⟨hdq,_⟩⟩
        exact ⟨by have hdpn := Nat.le_of_dvd (hA p hp) hdp; have hpn := hN p hp; omega,hdp,hdq⟩
      · rintro ⟨_,hdp,hdq⟩
        exact ⟨⟨hdp,(hA p hp).ne'⟩,⟨hdq,(hB q hq).ne'⟩⟩
    rw [hdiv,Finset.sum_filter]
  have hcount : (((A ×ˢ B).filter (fun pq => Nat.Coprime pq.1 pq.2)).card : ℝ) =
      ∑ p ∈ A, ∑ q ∈ B, if Nat.Coprime p q then (1 : ℝ) else 0 := by
    rw [← Finset.sum_product A B (fun pq : ℕ × ℕ => if Nat.Coprime pq.1 pq.2 then (1 : ℝ) else 0)]
    simp only [← Finset.sum_filter,Finset.sum_const,nsmul_eq_mul,mul_one]
  rw [hcount]
  calc _ = ∑ p ∈ A, ∑ q ∈ B, ∑ d ∈ Finset.range (N+1),
      if d ∣ p ∧ d ∣ q then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro p hp
        apply Finset.sum_congr rfl
        intro q hq
        exact hid p hp q hq
       _ = ∑ d ∈ Finset.range (N+1), ∑ p ∈ A, ∑ q ∈ B,
           if d ∣ p ∧ d ∣ q then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0 := by
        trans ∑ p ∈ A, ∑ d ∈ Finset.range (N+1), ∑ q ∈ B,
          if d ∣ p ∧ d ∣ q then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0
        · apply Finset.sum_congr rfl
          intro p hp
          exact Finset.sum_comm
        · exact Finset.sum_comm
       _ = _ := by
        apply Finset.sum_congr rfl
        intro d hd
        rw [← Finset.sum_product A B (fun pq : ℕ × ℕ => if d ∣ pq.1 ∧ d ∣ pq.2 then ((ArithmeticFunction.moebius d : ℤ) : ℝ) else 0),← Finset.sum_filter]
        have hfilter : ((A ×ˢ B).filter (fun pq => d ∣ pq.1 ∧ d ∣ pq.2)) =
            (A.filter (fun p => d ∣ p)) ×ˢ (B.filter (fun q => d ∣ q)) := by
          ext pq
          simp only [Finset.mem_filter,Finset.mem_product]
          tauto
        rw [hfilter,Finset.sum_const,Finset.card_product,nsmul_eq_mul,Nat.cast_mul]
        ring

end
end Paper14
