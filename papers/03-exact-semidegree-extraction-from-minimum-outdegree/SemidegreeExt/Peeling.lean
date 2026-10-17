import SemidegreeExt.Basic
import SemidegreeExt.Identities
import Mathlib.Tactic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.BigOperators

/-!
# Proposition 2.1: the sharp peeling bound
-/

open Finset Digraph Nat
open Classical

namespace SemidegreeExt

variable {n : ℕ} {G : Digraph (Fin n)} {d c : ℕ}

/-- A vertex of `S` whose semidegree in `G[S]` is at most `c` exists when `q G ≤ c`. -/
lemma exists_low_vertex (hc : q G ≤ c) {S : Finset (Fin n)} (hS : S.Nonempty) :
    ∃ v ∈ S, semiDegOn G S v ≤ c := by
  have h := le_q G hS
  have h2 : minSemiDegOn G S ≤ c := le_trans h hc
  rw [minSemiDegOn, dif_pos hS] at h2
  simpa [Finset.inf'_le_iff] using h2

/-- Deletion-order list obtained by repeatedly removing a low vertex. -/
noncomputable def peelOrder (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c)
    (S : Finset (Fin n)) : List (Fin n) :=
  if h0 : S = ∅ then
    []
  else
    have hS : S.Nonempty := Finset.nonempty_of_ne_empty h0
    have hlow : ∃ v ∈ S, semiDegOn G S v ≤ c := exists_low_vertex hc hS
    Classical.choose hlow :: peelOrder G c hc (S.erase (Classical.choose hlow))
  termination_by S.card
  decreasing_by
    have hmem : Classical.choose hlow ∈ S := (Classical.choose_spec hlow).1
    exact Finset.card_erase_lt_of_mem hmem

/-- Peel order of `S` lists exactly the elements of `S`, without repetition. -/
lemma peelOrder_eq (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c) :
    ∀ (k : ℕ) (S : Finset (Fin n)), S.card = k →
      (peelOrder G c hc S).toFinset = S ∧ (peelOrder G c hc S).Nodup := by
  intro k
  induction k with
  | zero =>
    intro S hcard
    have h0 : S = ∅ := Finset.card_eq_zero.1 hcard
    subst h0
    have heq : peelOrder G c hc ∅ = [] := by
      simp [peelOrder]
    rw [heq]
    simp
  | succ k ih =>
    intro S hcard
    by_cases h0 : S = ∅
    · subst h0
      simp at hcard
    · have hS : S.Nonempty := Finset.nonempty_of_ne_empty h0
      have hlow : ∃ v ∈ S, semiDegOn G S v ≤ c := exists_low_vertex hc hS
      set v := Classical.choose hlow
      have hmem : v ∈ S := (Classical.choose_spec hlow).1
      have hcardE : (S.erase v).card = k := by
        have := Finset.card_erase_of_mem hmem
        omega
      have hpeel : peelOrder G c hc S = v :: peelOrder G c hc (S.erase v) := by
        rw [peelOrder, dif_neg h0]
      obtain ⟨hfin, hnd⟩ := ih (S.erase v) hcardE
      rw [hpeel, List.toFinset_cons, hfin, Finset.insert_erase hmem,
        List.nodup_cons]
      refine ⟨rfl, ?_, hnd⟩
      intro hin
      have hin2 : v ∈ (peelOrder G c hc (S.erase v)).toFinset :=
        List.mem_toFinset.2 hin
      rw [hfin] at hin2
      exact absurd hin2 (Finset.notMem_erase v S)
      -- done

lemma peelOrder_toFinset (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c)
    (S : Finset (Fin n)) : (peelOrder G c hc S).toFinset = S :=
  (peelOrder_eq G c hc S.card S rfl).1

lemma peelOrder_nodup (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c) :
    (peelOrder G c hc univ).Nodup :=
  (peelOrder_eq G c hc univ.card univ rfl).2

lemma peelOrder_complete (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c) :
    (peelOrder G c hc univ).toFinset = univ :=
  peelOrder_toFinset G c hc univ

/-- Still-present vertex set when the `i`-th vertex of `L` is deleted:
those vertices whose index in `L` is at least `i`. -/
def peelPrefix (L : List (Fin n)) (i : ℕ) : Finset (Fin n) :=
  L.toFinset.filter fun u => i ≤ L.idxOf u

lemma mem_peelPrefix_iff {L : List (Fin n)} {i : ℕ} {u : Fin n} :
    u ∈ peelPrefix L i ↔ u ∈ L ∧ i ≤ L.idxOf u := by
  simp [peelPrefix]

/-- Type-O deletion certificate of `v` at its deletion time in `L`. -/
def typeOOf (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) (v : Fin n) : Prop :=
  outDegOn G (peelPrefix L (L.idxOf v)) v ≤ c

/-- Marked arcs relative to a deletion-order list `L` (head deleted first).
Each vertex has a single type: O if its outdegree at deletion is ≤ `c`, else I.
An arc `u → v` is marked when present in `G` and:
* `u` is deleted earlier and has type O (mark `u → v`), or
* `v` is deleted earlier and has type I (mark `u → v` as the reverse controlled direction). -/
noncomputable def markedOfList (G : Digraph (Fin n)) (c : ℕ) (L : List (Fin n)) :
    Finset (Fin n × Fin n) :=
  (univ.filter fun e : Fin n × Fin n =>
    G.Adj e.1 e.2 ∧
      let iu := L.idxOf e.1
      let iv := L.idxOf e.2
      if iu < iv then typeOOf G c L e.1
      else if iv < iu then ¬ typeOOf G c L e.2
      else False)

/-- Peel order of `S` is `v :: peelOrder (S.erase v)` with `v` low in `S`. -/
lemma peelOrder_cons (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c)
    {S : Finset (Fin n)} (h0 : S ≠ ∅) :
    ∃ v ∈ S, peelOrder G c hc S = v :: peelOrder G c hc (S.erase v) ∧
      semiDegOn G S v ≤ c := by
  have hS : S.Nonempty := Finset.nonempty_of_ne_empty h0
  have hlow : ∃ v ∈ S, semiDegOn G S v ≤ c := exists_low_vertex hc hS
  refine ⟨Classical.choose hlow, (Classical.choose_spec hlow).1, ?_,
    (Classical.choose_spec hlow).2⟩
  rw [peelOrder, dif_neg h0]

/-- `peelPrefix L 0` is the full vertex set of `L`. -/
lemma peelPrefix_zero (L : List (Fin n)) : peelPrefix L 0 = L.toFinset := by
  ext u
  simp [mem_peelPrefix_iff]

/-- Prefix of a cons list after the head, relative to a later vertex.
Requires the head is not in the tail (as in a nodup peel order). -/
lemma peelPrefix_cons_ne {L : List (Fin n)} {w v : Fin n}
    (hvw : v ≠ w) (hwn : w ∉ L) :
    peelPrefix (w :: L) ((w :: L).idxOf v) = peelPrefix L (L.idxOf v) := by
  have hidx : (w :: L).idxOf v = L.idxOf v + 1 :=
    List.idxOf_cons_ne L (Ne.symm hvw)
  ext u
  simp only [mem_peelPrefix_iff, List.mem_cons]
  by_cases huw : u = w
  · subst huw
    have h0 : (u :: L).idxOf u = 0 := List.idxOf_cons_self
    -- LHS: u ∈ (u::L) and (u::L).idxOf v ≤ 0, impossible
    have hLHS : ¬ ((True ∨ u ∈ L) ∧ ((u :: L).idxOf v ≤ (u :: L).idxOf u)) := by
      simp [h0]
      omega
    have hRHS : ¬ (u ∈ L ∧ L.idxOf v ≤ L.idxOf u) := by
      intro ⟨hin, _⟩
      exact hwn hin
    simp only [hLHS, hRHS]
  · have hidxu : (w :: L).idxOf u = L.idxOf u + 1 :=
      List.idxOf_cons_ne L (Ne.symm huw)
    rw [hidx, hidxu]
    constructor
    · intro ⟨hmem, hi⟩
      refine ⟨?_, by omega⟩
      rcases hmem with h | h
      · exact absurd h huw
      · exact h
    · intro ⟨hmem, hi⟩
      exact ⟨Or.inr hmem, by omega⟩

/-- Control: when `v` is deleted at position `idxOf v`, the remaining set is the
corresponding prefix and `semiDegOn` of `v` there is at most `c`. -/
lemma peelOrder_control (G : Digraph (Fin n)) (c : ℕ) (hc : q G ≤ c)
    (v : Fin n) (hv : v ∈ peelOrder G c hc univ) :
    semiDegOn G (peelPrefix (peelOrder G c hc univ)
      ((peelOrder G c hc univ).idxOf v)) v ≤ c := by
  suffices hgen : ∀ S : Finset (Fin n), ∀ v : Fin n, v ∈ peelOrder G c hc S →
      semiDegOn G (peelPrefix (peelOrder G c hc S)
        ((peelOrder G c hc S).idxOf v)) v ≤ c by
    exact hgen univ v hv
  intro S
  induction hcard : S.card generalizing S with
  | zero =>
    intro v hv
    have h0 : S = ∅ := Finset.card_eq_zero.1 hcard
    subst h0
    simp [peelOrder] at hv
  | succ k ih =>
    intro v hv
    by_cases h0 : S = ∅
    · subst h0
      simp at hcard
    · obtain ⟨w, hw, hpeel, hwlow⟩ := peelOrder_cons G c hc h0
      rw [hpeel] at hv
      rw [hpeel]
      by_cases hvw : v = w
      · subst hvw
        rw [List.idxOf_cons_self, peelPrefix_zero]
        have hS : ((v :: peelOrder G c hc (S.erase v)).toFinset) = S := by
          rw [List.toFinset_cons, peelOrder_toFinset G c hc (S.erase v),
            Finset.insert_erase hw]
        rw [hS]
        exact hwlow
      · have hvin : v ∈ peelOrder G c hc (S.erase w) := by
          rw [List.mem_cons] at hv
          exact hv.resolve_left hvw
        have hih := ih (S.erase w) (by
          have := Finset.card_erase_of_mem hw
          omega) v hvin
        have hwn : w ∉ peelOrder G c hc (S.erase w) := by
          intro hin
          have hin2 : w ∈ (peelOrder G c hc (S.erase w)).toFinset :=
            List.mem_toFinset.2 hin
          rw [peelOrder_toFinset G c hc (S.erase w)] at hin2
          exact Finset.notMem_erase w S hin2
        rw [peelPrefix_cons_ne hvw hwn]
        exact hih

/-- Charge each marked arc to the earlier-deleted endpoint. -/
noncomputable def chargeTo (L : List (Fin n)) (e : Fin n × Fin n) : Fin n :=
  if L.idxOf e.1 < L.idxOf e.2 then e.1 else e.2

/-- Number of vertices deleted after `v` in `L`. -/
def laterCount (L : List (Fin n)) (v : Fin n) : ℕ := L.length - 1 - L.idxOf v

/-- Min semidegree of `G[S]` is at most `S.card`. -/
lemma minSemiDegOn_le_card (G : Digraph (Fin n)) (S : Finset (Fin n)) :
    minSemiDegOn G S ≤ S.card := by
  by_cases hS : S.Nonempty
  · rw [minSemiDegOn, dif_pos hS]
    have hiff : S.inf' hS (semiDegOn G S) ≤ S.card ↔ ∃ i ∈ S, semiDegOn G S i ≤ S.card :=
      Finset.inf'_le_iff hS
    exact hiff.2 ⟨hS.choose, hS.choose_spec, by
        unfold semiDegOn
        exact le_trans (min_le_left _ _) (outDegOn_le_card G S hS.choose)⟩
  · rw [minSemiDegOn, dif_neg hS]
    exact Nat.zero_le _

/-- `q G ≤ n` for any `n`-vertex digraph. -/
lemma q_le_n (G : Digraph (Fin n)) : q G ≤ n := by
  unfold q
  refine Finset.sup_le fun S _ => ?_
  refine le_trans (minSemiDegOn_le_card G S) ?_
  have := S.card_le_univ
  rwa [Fintype.card_fin] at this

end SemidegreeExt
