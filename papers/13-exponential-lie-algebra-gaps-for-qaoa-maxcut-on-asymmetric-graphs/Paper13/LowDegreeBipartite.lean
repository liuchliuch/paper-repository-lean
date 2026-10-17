import Mathlib.Combinatorics.SimpleGraph.ConcreteColorings
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.WalkDecomp
noncomputable section
namespace Paper13
open SimpleGraph
attribute [local instance] Classical.propDecidable

lemma walk_tail_penultimate {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (h : 2 ≤ p.length) : p.tail.penultimate=p.penultimate := by
  cases p with
  | nil => simp at h
  | cons ha p =>
    cases p with
    | nil => simp at h
    | cons hb p => rfl

lemma walk_dropLast_length {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) :
    p.dropLast.length=p.length-1 := by simp [Walk.dropLast,Nat.min_eq_left (Nat.sub_le _ _)]

/-- A globally shortest odd loop has two distinct neighbours of its base point. -/
lemma shortest_odd_loop_neighbours {V : Type*} {G : SimpleGraph V} {u : V} (p : G.Walk u u)
    (ho : Odd p.length) (hm : ∀ (v : V) (q : G.Walk v v), Odd q.length → p.length ≤ q.length) :
    p.snd≠p.penultimate := by
  have hl : 3 ≤ p.length := by
    cases p with
    | nil => simp at ho
    | cons h p =>
      cases p with
      | nil => exact False.elim (G.loopless _ h)
      | cons h' p => have := ho; rw [Nat.odd_iff] at this; simp only [Walk.length_cons] at this ⊢; omega
  intro he
  have hend : p.tail.penultimate=p.snd := (walk_tail_penultimate p (by omega)).trans he.symm
  let q : G.Walk p.snd p.snd := p.tail.dropLast.copy rfl hend
  have hlen : q.length=p.length-2 := by
    dsimp [q]
    rw [Walk.length_copy,walk_dropLast_length]
    have hp : ¬ p.Nil := by intro h; have := (Walk.nil_iff_length_eq.mp h); omega
    have ht := Walk.length_tail_add_one hp
    omega
  have hq : Odd q.length := by rw [hlen,Nat.odd_iff]; rw [Nat.odd_iff] at ho; omega
  have := hm _ q hq
  omega

/-- With maximum degree two, a connected non-bipartite graph is 2-regular. -/
theorem regular_two_of_nonbip_low_degree {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (hnb : ¬ Nonempty (G.Coloring (Fin 2))) (hd : ∀ v, G.degree v ≤ 2) : G.IsRegularOfDegree 2 := by
  have hex : ∃ m, ∃ u : V, ∃ p : G.Walk u u, Odd p.length ∧ p.length=m := by
    have hn : ¬∀ u, ∀ p : G.Walk u u, Even p.length := fun h => hnb (two_colorable_iff_forall_loop_even.mpr h)
    push_neg at hn
    obtain ⟨u,p,hp⟩ := hn
    exact ⟨p.length,u,p,Nat.not_even_iff_odd.mp hp,rfl⟩
  obtain ⟨u,p,ho,hlen⟩ := Nat.find_spec hex
  have hmin : ∀ (v : V) (q : G.Walk v v), Odd q.length → p.length ≤ q.length := by
    intro v q hq
    rw [hlen]
    exact Nat.find_min' hex ⟨v,q,hq,rfl⟩
  have htwo : ∀ v ∈ p.support, ∃ a ∈ p.support, ∃ b ∈ p.support, a≠b ∧ G.Adj v a ∧ G.Adj v b := by
    intro v hv
    let q := p.rotate hv
    have hqLen : q.length=p.length := by
      dsimp [q,Walk.rotate]
      rw [Walk.length_append,add_comm,←Walk.length_append,Walk.take_spec]
    have hqOdd : Odd q.length := hqLen ▸ ho
    have hqMin : ∀ (t : V) (r : G.Walk t t), Odd r.length → q.length ≤ r.length := by
      intro t r hr; rw [hqLen]; exact hmin t r hr
    have hsub : q.support ⊆ p.support := by
      intro x hx
      change x ∈ ((p.dropUntil v hv).append (p.takeUntil v hv)).support at hx
      rw [Walk.support_append] at hx
      rcases List.mem_append.mp hx with h | h
      · exact p.support_dropUntil_subset hv h
      · exact p.support_takeUntil_subset hv (List.mem_of_mem_tail h)
    have hqNil : ¬ q.Nil := by intro h; have hz := (Walk.nil_iff_length_eq.mp h); rw [hz] at hqOdd; simp at hqOdd
    exact ⟨q.snd,hsub (q.getVert_mem_support 1),q.penultimate,hsub (q.getVert_mem_support _),
      shortest_odd_loop_neighbours q hqOdd hqMin,q.adj_snd hqNil,G.symm (q.adj_penultimate hqNil)⟩
  have hclosed : ∀ v ∈ p.support, ∀ w, G.Adj v w → w ∈ p.support := by
    intro v hv w hvw
    obtain ⟨a,ha,b,hb,hab,hva,hvb⟩ := htwo v hv
    have hS : G.neighborFinset v={a,b} := by
      have hsub : ({a,b} : Finset V) ⊆ G.neighborFinset v := by intro x hx; simp only [Finset.mem_insert,Finset.mem_singleton] at hx; rcases hx with rfl | rfl <;> simpa using (show G.Adj v _ from by assumption)
      symm
      apply Finset.eq_of_subset_of_card_le hsub
      simpa [Finset.card_pair hab] using hd v
    have hw : w ∈ G.neighborFinset v := by simpa using hvw
    rw [hS] at hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at hw
    rcases hw with rfl | rfl <;> assumption
  have hall : ∀ v, v ∈ p.support := by
    have hwalk : ∀ {x y : V}, G.Walk x y → x ∈ p.support → y ∈ p.support := by
      intro x y q
      induction q with
      | nil => exact id
      | @cons x y z hxy q ih => exact fun hx => ih (hclosed x hx y hxy)
    intro v
    exact (hc u v).elim (fun q => hwalk q p.start_mem_support)
  intro v
  obtain ⟨a,ha,b,hb,hab,hva,hvb⟩ := htwo v (hall v)
  have hsub : ({a,b} : Finset V) ⊆ G.neighborFinset v := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simpa using (show G.Adj v _ from by assumption)
  have hle := Finset.card_le_card hsub
  have hlo : 2 ≤ G.degree v := by simpa [Finset.card_pair hab] using hle
  exact Nat.le_antisymm (hd v) hlo
end Paper13
