import SemidegreeExt.Peeling
import SemidegreeExt.Charge
import SemidegreeExt.Tournament
import SemidegreeExt.Identities
import Mathlib.Tactic

/-!
# Proposition 2.1 assembly

Combines the marking counts: upper bound `marked_charge_le'` and lower bound
`marked_tournament_ge`.
-/

open Finset Digraph Nat
open Classical

namespace SemidegreeExt

variable {n : ℕ} {G : Digraph (Fin n)} {d c : ℕ}

/-- Proposition 2.1 (sharp peeling bound). -/
theorem prop_2_1 {n : ℕ} {G : Digraph (Fin n)} {d c : ℕ}
    (hG : Loopless G) (hd : ∀ v, d ≤ outDeg G v) (hc : c = q G)
    (hn : 0 < n) (hdn : d < n) :
    d * (d + 1) + c * (c + 1) ≤ 2 * c * n := by
  have hc_le : q G ≤ c := le_of_eq hc.symm
  have hcn : c ≤ n := by
    have hqn := q_le_n G
    have : q G = c := hc.symm
    omega
  have hcharge := marked_charge_le' G c hc_le
  have hcomplete := peelOrder_complete G c hc_le
  have hnd := peelOrder_nodup G c hc_le
  have hlen : (peelOrder G c hc_le univ).length = n := by
    have h1 : (peelOrder G c hc_le univ).toFinset.card = n := by
      rw [hcomplete]
      exact Fintype.card_fin n
    have h2 : (peelOrder G c hc_le univ).toFinset.card
        = (peelOrder G c hc_le univ).length := by
      show (peelOrder G c hc_le univ).dedup.length
        = (peelOrder G c hc_le univ).length
      rw [List.dedup_eq_self.2 hnd]
    omega
  have htour := marked_tournament_ge' G c (peelOrder G c hc_le univ)
    hG hcomplete hnd hlen hd hn hdn
  have hsum := sum_min_eq n c hcn
  have h2 : d * (d + 1) ≤ (markedOfList G c (peelOrder G c hc_le univ)).card * 2 := by
    have h := Nat.mul_le_mul_left 2 htour
    have heven : 2 * (d * (d + 1) / 2) = d * (d + 1) := by
      have hdiv := Nat.mul_div_cancel' (Even.two_dvd (Nat.even_mul_succ_self d))
      omega
    omega
  omega

end SemidegreeExt
