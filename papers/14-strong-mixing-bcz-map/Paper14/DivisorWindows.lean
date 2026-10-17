import Paper14.MoebiusCoprime
import Mathlib.Data.Nat.Factorization.Basic

open Finset Filter Topology
namespace Paper14

/-- Exact positive-multiple count in an arbitrary integer window. -/
lemma Ioc_filter_dvd_card (L U d : ℕ) :
    ((Finset.Ioc L U).filter (fun k => d ∣ k)).card = U/d-L/d := by
  by_cases hLU : L ≤ U
  · have heq : ((Finset.Ioc 0 U).filter (fun k => d ∣ k)) =
        ((Finset.Ioc 0 L).filter (fun k => d ∣ k)) ∪
          ((Finset.Ioc L U).filter (fun k => d ∣ k)) := by
      ext k
      simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_union]
      omega
    have hd : Disjoint ((Finset.Ioc 0 L).filter (fun k => d ∣ k))
        ((Finset.Ioc L U).filter (fun k => d ∣ k)) := by
      apply Finset.disjoint_left.mpr
      intro k hk hk'
      simp only [Finset.mem_filter,Finset.mem_Ioc] at hk hk'
      omega
    have hcard := congrArg Finset.card heq
    rw [Finset.card_union_of_disjoint hd,Nat.Ioc_filter_dvd_card_eq_div,Nat.Ioc_filter_dvd_card_eq_div] at hcard
    omega
  · have hemp : Finset.Ioc L U = ∅ := by apply Finset.Ioc_eq_empty; omega
    rw [hemp,Finset.filter_empty,Finset.card_empty]
    exact (Nat.sub_eq_zero_of_le (Nat.div_le_div_right (by omega))).symm

/-- The Appendix A count uses these exact open-left integer windows. -/
lemma coprimePairCount_eq_Ioc (n : ℕ) : coprimePairCount n =
    ((Finset.Ioc (n/6) (n/3) ×ˢ Finset.Ioc ((n-1)/2) n).filter
      (fun pq => Nat.Coprime pq.1 pq.2)).card := by
  by_cases hn : n = 0
  · simp [hn,coprimePairCount]
  have hp : Finset.Icc (n/6+1) (n/3) = Finset.Ioc (n/6) (n/3) := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  have hq : Finset.Icc ((n+1)/2) n = Finset.Ioc ((n-1)/2) n := by
    ext k
    simp only [Finset.mem_Icc,Finset.mem_Ioc]
    omega
  simp only [coprimePairCount,hp,hq]

end Paper14
