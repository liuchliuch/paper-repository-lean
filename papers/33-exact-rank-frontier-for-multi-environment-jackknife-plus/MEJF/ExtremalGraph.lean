import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Abel
import Lean.Elab.Tactic.Omega

/-! # Extremal oriented graphs (paper Lemma 5.1)

The construction is explicit: short forward arcs on a cyclic group, then a regular
odd tournament on the selected vertices with all arcs directed to its complement.
-/

namespace MEJF.ExtremalGraph

open Finset

/-- Number of distinct outgoing neighbours. -/
noncomputable def outdegree {α : Type*} [Fintype α] (R : α → α → Prop) (u : α) : ℕ := by
  classical
  exact (Finset.univ.filter (R u)).card

/-- The first `k` positive forward steps of the cyclic group `Fin n`. -/
def cyclicArc {n : ℕ} [NeZero n] (k : ℕ) (u v : Fin n) : Prop :=
  0 < (v - u).val ∧ (v - u).val ≤ k

/-- No two opposite short forward steps can occur when twice the radius is less
than the circumference. -/
theorem cyclicArc_asymmetric {n k : ℕ} [NeZero n] (hk : 2 * k < n) :
    ∀ u v : Fin n, cyclicArc k u v → ¬ cyclicArc k v u := by
  intro u v huv hvu
  have hsmall : (v-u).val + (u-v).val < n := by
    obtain ⟨_, huv⟩ := huv
    obtain ⟨_, hvu⟩ := hvu
    omega
  have hzero : (v-u) + (u-v) = (0 : Fin n) := by abel
  have heq := congrArg Fin.val hzero
  rw [Fin.val_add_eq_of_add_lt hsmall] at heq
  simp only [Fin.val_zero] at heq
  exact (Nat.ne_of_gt huv.1) (by omega)

/-- At odd size `2*k+1`, every distinct pair has a forward arc in one
direction. Together with `cyclicArc_asymmetric`, this is a regular tournament. -/
theorem cyclicArc_total {n k : ℕ} [NeZero n] (hn : n = 2*k+1)
    (u v : Fin n) (huv : u ≠ v) : cyclicArc k u v ∨ cyclicArc k v u := by
  have hp : 0 < (v-u).val := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hz' : v-u = 0 := Fin.ext hz
    exact huv (sub_eq_zero.mp hz').symm
  have hq : 0 < (u-v).val := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hz' : u-v = 0 := Fin.ext hz
    exact huv (sub_eq_zero.mp hz')
  have hmod : ((v-u).val + (u-v).val) % n = 0 := by
    have hzero : (v-u) + (u-v) = (0 : Fin n) := by abel
    simpa only [Fin.val_add, Fin.val_zero] using congrArg Fin.val hzero
  have hpbound := (v-u).is_lt
  have hqbound := (u-v).is_lt
  have hsum : (v-u).val + (u-v).val = n := by
    by_cases hsmall : (v-u).val + (u-v).val < n
    · rw [Nat.mod_eq_of_lt hsmall] at hmod
      omega
    · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hmod
      omega
  by_cases h : (v-u).val ≤ k
  · exact Or.inl ⟨hp, h⟩
  · exact Or.inr ⟨hq, by omega⟩

/-- Translation identifies the outgoing neighbours with the positive steps
`1, …, k`, represented by `Fin k`. -/
noncomputable def cyclicNeighbourEquiv {n k : ℕ} [NeZero n] (hk : k < n) (u : Fin n) :
    {v : Fin n // cyclicArc k u v} ≃ Fin k where
  toFun v := ⟨(v.val-u).val - 1, by have := v.property; unfold cyclicArc at this; omega⟩
  invFun r := ⟨u + ⟨r.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt r.is_lt) hk⟩, by
    simp only [cyclicArc, add_sub_cancel_left]
    exact ⟨Nat.zero_lt_succ _, Nat.succ_le_of_lt r.is_lt⟩⟩
  left_inv v := by
    apply Subtype.ext
    have hv := v.property.1
    have hvn := (v.val-u).is_lt
    dsimp
    have heq : (⟨(v.val-u).val - 1 + 1, by omega⟩ : Fin n) = v.val-u := by
      apply Fin.ext
      have := v.property.1
      change (v.val-u).val - 1 + 1 = (v.val-u).val
      omega
    rw [heq]
    abel
  right_inv r := by
    apply Fin.ext
    simp only [add_sub_cancel_left, Nat.add_sub_cancel, Fin.val_mk]

/-- Every vertex in the cyclic construction has exactly `k` outgoing neighbours. -/
theorem cyclicArc_outdegree {n k : ℕ} [NeZero n] (hk : k < n) (u : Fin n) :
    outdegree (cyclicArc k) u = k := by
  classical
  have h := Fintype.card_congr (cyclicNeighbourEquiv hk u)
  simpa [outdegree, Fintype.card_subtype] using h

/-- Transporting a relation along a bijection preserves each outdegree. -/
theorem outdegree_transport {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (R : α → α → Prop) (u : β) :
    outdegree (fun x y => R (e.symm x) (e.symm y)) u = outdegree R (e.symm u) := by
  classical
  unfold outdegree
  refine Finset.card_bij (fun v _ => e.symm v) ?_ ?_ ?_
  · intro v hv
    simpa only [mem_filter, mem_univ, true_and] using hv
  · intro a ha b hb hab
    exact e.symm.injective hab
  · intro v hv
    refine ⟨e v, ?_, e.symm_apply_apply v⟩
    simpa only [mem_filter, mem_univ, true_and, e.symm_apply_apply] using hv

/-- Keep a graph on the selected summand, direct all arcs out to the other
summand, and leave the other summand with no outgoing arcs. -/
def outwardJoin {α β : Type*} (R : α → α → Prop) : (α ⊕ β) → (α ⊕ β) → Prop
  | .inl u, .inl v => R u v
  | .inl _, .inr _ => True
  | .inr _, _ => False

theorem outwardJoin_asymmetric {α β : Type*} (R : α → α → Prop)
    (hR : ∀ u v, R u v → ¬ R v u) :
    ∀ u v : α ⊕ β, outwardJoin R u v → ¬ outwardJoin R v u := by
  rintro (u | u) (v | v) huv hvu
  · exact hR u v huv hvu
  · exact hvu
  · exact huv
  · exact huv

theorem outwardJoin_outdegree_left {α β : Type*} [Fintype α] [Fintype β]
    (R : α → α → Prop) (u : α) :
    outdegree (outwardJoin (β := β) R) (.inl u) = outdegree R u + Fintype.card β := by
  classical
  have heq : (univ.filter (outwardJoin (β := β) R (.inl u))) =
      (univ.filter (R u)).disjSum (univ : Finset β) := by
    ext v
    rcases v with v | v <;> simp [outwardJoin]
  unfold outdegree
  rw [heq, card_disjSum, card_univ]

theorem outwardJoin_outdegree_right {α β : Type*} [Fintype α] [Fintype β]
    (R : α → α → Prop) (u : β) :
    outdegree (outwardJoin R) (.inr u) = 0 := by
  classical
  simp [outdegree, outwardJoin]

/-- A cyclic graph on `s` selected vertices with all arcs directed to `d`
remaining vertices, transported to the specified vertex type `Fin N`. -/
theorem cyclic_join_construction (N s d k : ℕ) (hs : 0 < s)
    (hk : 2 * k < s) (hsize : s + d = N) :
    ∃ (R : Fin N → Fin N → Prop) (S : Finset (Fin N)),
      (∀ u v, R u v → ¬ R v u) ∧ S.card = s ∧
      (∀ u ∈ S, outdegree R u = k + d) ∧
      (∀ u ∉ S, outdegree R u = 0) := by
  classical
  letI : NeZero s := ⟨by omega⟩
  let e : (Fin s ⊕ Fin d) ≃ Fin N := finSumFinEquiv.trans (finCongr hsize)
  let Q := outwardJoin (β := Fin d) (cyclicArc k : Fin s → Fin s → Prop)
  let R : Fin N → Fin N → Prop := fun u v => Q (e.symm u) (e.symm v)
  let S₀ : Finset (Fin s ⊕ Fin d) := (univ : Finset (Fin s)).map Function.Embedding.inl
  let S : Finset (Fin N) := S₀.map e.toEmbedding
  refine ⟨R, S, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    exact outwardJoin_asymmetric _ (cyclicArc_asymmetric hk) (e.symm u) (e.symm v) huv
  · simp [S, S₀]
  · intro u hu
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hu
    obtain ⟨a, ha, rfl⟩ := mem_map.mp hx
    change outdegree (fun x y => Q (e.symm x) (e.symm y)) (e (.inl a)) = k+d
    rw [outdegree_transport, e.symm_apply_apply, outwardJoin_outdegree_left]
    rw [cyclicArc_outdegree (by omega)]
    simp
  · intro u hu
    change outdegree (fun x y => Q (e.symm x) (e.symm y)) u = 0
    rw [outdegree_transport]
    cases he : e.symm u with
    | inl a =>
        exfalso
        apply hu
        refine mem_map.mpr ⟨.inl a, ?_, ?_⟩
        · exact mem_map.mpr ⟨a, mem_univ a, rfl⟩
        · change e (.inl a) = u
          rw [← he, e.apply_symm_apply]
    | inr a =>
        exact outwardJoin_outdegree_right _ a

/-- Paper Lemma 5.1: an extremal oriented graph with exactly the asserted
number of selected vertices, all of outdegree exactly `w`. The explicit
construction also leaves all unselected vertices with outdegree zero. -/
theorem exists_extremal_oriented_graph (N w : ℕ) (hN : 2 ≤ N) (hw : w < N) :
    ∃ (R : Fin N → Fin N → Prop) (S : Finset (Fin N)),
      (∀ u v, R u v → ¬ R v u) ∧
      S.card = min N (2 * (N-w) - 1) ∧
      (∀ u ∈ S, outdegree R u = w) ∧
      (∀ u ∉ S, outdegree R u = 0) := by
  by_cases hlo : 2*w < N
  · obtain ⟨R, S, hR, hS, hdeg, hout⟩ :=
      cyclic_join_construction N N 0 w (by omega) hlo (by omega)
    refine ⟨R, S, hR, ?_, ?_, hout⟩
    · rw [hS, min_eq_left]
      omega
    · simpa using hdeg
  · let s := 2*(N-w)-1
    let d := N-s
    let k := N-w-1
    have hs : 0 < s := by dsimp [s]; omega
    have hks : 2*k < s := by dsimp [s, k]; omega
    have hsize : s+d=N := by dsimp [s, d]; omega
    have hkd : k+d=w := by dsimp [k, d, s]; omega
    obtain ⟨R, S, hR, hS, hdeg, hout⟩ :=
      cyclic_join_construction N s d k hs hks hsize
    refine ⟨R, S, hR, ?_, ?_, hout⟩
    · rw [hS, min_eq_right]
      dsimp [s]
      omega
    · simpa only [hkd] using hdeg

end MEJF.ExtremalGraph
