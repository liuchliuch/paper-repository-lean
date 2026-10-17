import Mathlib.Tactic
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
open Finset
namespace SemidegreeExt.FlowAlgorithm

abbrev Matrix (V : Type*) := V → V → ℤ
/-- Explicit finite input enumeration. Algorithm execution never extracts a
list by noncomputable choice from a finite-set quotient. -/
class Enumeration (V : Type*) where
  elems : List V
  nodup : elems.Nodup
  complete : ∀ v, v ∈ elems

instance (n : ℕ) : Enumeration (Fin n) where
  elems := List.finRange n
  nodup := List.nodup_finRange n
  complete := by intro v; simp

instance {A B : Type*} [Enumeration A] [Enumeration B] : Enumeration (A ⊕ B) where
  elems := (Enumeration.elems (V := A)).map Sum.inl ++ (Enumeration.elems (V := B)).map Sum.inr
  nodup := by
    rw [List.nodup_append]
    refine ⟨Enumeration.nodup.map Sum.inl_injective, Enumeration.nodup.map Sum.inr_injective, ?_⟩
    intro x hx y hy heq
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hy
    cases heq
  complete := by
    intro v
    cases v with
    | inl a => exact List.mem_append_left _ (List.mem_map.mpr ⟨a, Enumeration.complete a, rfl⟩)
    | inr b => exact List.mem_append_right _ (List.mem_map.mpr ⟨b, Enumeration.complete b, rfl⟩)

instance {A B : Type*} [Enumeration A] [Enumeration B] : Enumeration (A × B) where
  elems := (Enumeration.elems (V := A)).product (Enumeration.elems (V := B))
  nodup := List.Nodup.product Enumeration.nodup Enumeration.nodup
  complete := by
    intro v
    change v ∈ ((Enumeration.elems (V := A)) ×ˢ (Enumeration.elems (V := B)))
    exact List.mem_product.mpr ⟨Enumeration.complete v.1,Enumeration.complete v.2⟩

variable {V : Type*} [Fintype V] [DecidableEq V]

def divergence (f : Matrix V) (v : V) : ℤ := ∑ w, f v w

def Skew (f : Matrix V) : Prop := ∀ u v, f u v = -f v u

def Bounded (cap : V → V → ℕ) (f : Matrix V) : Prop := ∀ u v, f u v ≤ cap u v

/-- Standard antisymmetric integral flow; a zero reverse capacity forces the
usual forward flow to be nonnegative. -/
def Valid (cap : V → V → ℕ) (s t : V) (f : Matrix V) : Prop :=
  Skew f ∧ Bounded cap f ∧ ∀ v, v ≠ s → v ≠ t → divergence f v = 0

def delta (a b u v : V) : ℤ :=
  (if u=a ∧ v=b then 1 else 0) - (if u=b ∧ v=a then 1 else 0)

def addEdge (f : Matrix V) (a b : V) : Matrix V := fun u v => f u v + delta a b u v

/-- A route is stored in reverse edge order. Evaluation visits each stored edge once. -/
def applyRoute (f : Matrix V) : List (V × V) → Matrix V
  | [] => f
  | (a,b)::es => addEdge (applyRoute f es) a b

lemma delta_skew (a b u v : V) : delta a b u v = -delta a b v u := by
  simp only [delta, and_comm]
  ring

lemma divergence_addEdge (f : Matrix V) (a b v : V) :
    divergence (addEdge f a b) v = divergence f v +
      (if v=a then 1 else 0) - (if v=b then 1 else 0) := by
  simp only [divergence, addEdge, delta, sum_add_distrib, sum_sub_distrib]
  have h (x y : V) : (∑ w : V, if v=x ∧ w=y then (1 : ℤ) else 0) = if v=x then 1 else 0 := by
    by_cases hv : v=x <;> simp [hv]
  rw [h, h]
  ring

lemma skew_addEdge {f : Matrix V} (hf : Skew f) (a b : V) : Skew (addEdge f a b) := by
  intro u v
  simp only [addEdge, hf u v, delta_skew a b u v]
  ring

lemma bounded_addEdge {cap : V → V → ℕ} {f g : Matrix V} {a b : V}
    (hg : Bounded cap g) (hab : a ≠ b) (hres : f a b < cap a b)
    (heq : g a b = f a b) : Bounded cap (addEdge g a b) := by
  intro u v
  by_cases hforward : u=a ∧ v=b
  · have huv : u=a := hforward.1
    have hvv : v=b := hforward.2
    subst u; subst v
    simp only [addEdge, delta, hab, Ne.symm hab, and_self, if_true,
      false_and, if_false, sub_zero, heq]
    omega
  · by_cases hback : u=b ∧ v=a
    · have huv : u=b := hback.1
      have hvv : v=a := hback.2
      subst u; subst v
      have hh := hg b a
      simp [addEdge, delta, hab, Ne.symm hab]
      omega
    · simpa only [addEdge, delta, if_neg hforward, if_neg hback, sub_self, add_zero] using hg u v

/-- A discovery table is a finite list of predecessor edges, newest first.
Every lookup follows exactly one recursive branch per table entry. -/
def lookupRoute : List (V × V) → V → List (V × V)
  | [], _ => []
  | (a,b)::es, v => if v=b then (a,b)::lookupRoute es a else lookupRoute es v

structure SearchState (V : Type*) where
  seen : Finset V
  table : List (V × V)

def SearchState.routes (st : SearchState V) (v : V) := lookupRoute st.table v

variable [Enumeration V]

def vertices : List V := Enumeration.elems

@[simp] lemma mem_vertices (v : V) : v ∈ vertices := Enumeration.complete v

@[simp] lemma vertices_length : (vertices (V := V)).length = Fintype.card V := by
  have h : (vertices (V := V)).toFinset = univ := by ext v; simp
  calc
    _ = (vertices (V := V)).toFinset.card := (List.toFinset_card_of_nodup (Enumeration.nodup (V := V))).symm
    _ = _ := by rw [h,card_univ]

def pairs : List (V × V) := (vertices (V := V)).flatMap fun a => (vertices (V := V)).map fun b => (a,b)

@[simp] lemma mem_pairs (e : V × V) : e ∈ pairs := by
  obtain ⟨a,b⟩ := e
  simp [pairs]

def frontier (cap : V → V → ℕ) (f : Matrix V) (S : Finset V) : Option (V × V) :=
  (pairs (V := V)).find? fun e =>
    decide (e.1 ∈ S ∧ e.2 ∉ S ∧ f e.1 e.2 < cap e.1 e.2)

def Closed (cap : V → V → ℕ) (f : Matrix V) (S : Finset V) : Prop :=
  ∀ a ∈ S, ∀ b ∉ S, (cap a b : ℤ) ≤ f a b

lemma frontier_some {cap : V → V → ℕ} {f : Matrix V} {S : Finset V} {a b : V}
    (h : frontier cap f S = some (a,b)) : a ∈ S ∧ b ∉ S ∧ f a b < cap a b := by
  have hp : (decide (a ∈ S ∧ b ∉ S ∧ f a b < cap a b)) = true :=
    List.find?_some (p := fun e : V × V => decide (e.1 ∈ S ∧ e.2 ∉ S ∧ f e.1 e.2 < cap e.1 e.2)) h
  exact of_decide_eq_true hp

lemma frontier_none_iff (cap : V → V → ℕ) (f : Matrix V) (S : Finset V) :
    frontier cap f S = none ↔ Closed cap f S := by
  unfold frontier
  rw [List.find?_eq_none]
  constructor
  · intro h a ha b hb
    have hh := h (a,b) (mem_pairs _)
    simp only [decide_eq_true_eq] at hh
    exact le_of_not_gt (fun hr => hh ⟨ha,hb,hr⟩)
  · intro h e _
    simp only [decide_eq_true_eq]
    intro he
    exact not_lt_of_ge (h e.1 he.1 e.2 he.2.1) he.2.2

def searchStep (cap : V → V → ℕ) (f : Matrix V) (st : SearchState V) : SearchState V :=
  match frontier cap f st.seen with
  | none => st
  | some (a,b) => ⟨insert b st.seen, (a,b)::st.table⟩

def search (cap : V → V → ℕ) (f : Matrix V) (s : V) : ℕ → SearchState V
  | 0 => ⟨{s}, []⟩
  | k+1 => searchStep cap f (search cap f s k)

/-- Every stored candidate is an actual sequence of unit residual updates.
The support condition ensures that appending a newly discovered vertex cannot
reuse an edge of that route. -/
def SearchInvariant (cap : V → V → ℕ) (f : Matrix V) (s : V) (st : SearchState V) : Prop :=
  s ∈ st.seen ∧ ∀ a ∈ st.seen,
    Skew (applyRoute f (st.routes a)) ∧ Bounded cap (applyRoute f (st.routes a)) ∧
    (∀ v, divergence (applyRoute f (st.routes a)) v = divergence f v +
      (if v=s then 1 else 0) - (if v=a then 1 else 0)) ∧
    (∀ u v, u ∉ st.seen ∨ v ∉ st.seen → applyRoute f (st.routes a) u v = f u v) ∧
    (st.routes a).length + 1 ≤ st.seen.card

lemma searchStep_invariant {cap : V → V → ℕ} {f : Matrix V} {s : V} {st : SearchState V}
    (hi : SearchInvariant cap f s st) : SearchInvariant cap f s (searchStep cap f st) := by
  cases he : frontier cap f st.seen with
  | none => simpa only [searchStep, he] using hi
  | some e =>
    obtain ⟨a,b⟩ := e
    simp only [searchStep, he]
    have hr := frontier_some he
    have hab : a ≠ b := by intro h; exact hr.2.1 (h ▸ hr.1)
    have hcard := card_insert_of_notMem hr.2.1
    refine ⟨mem_insert_of_mem hi.1, ?_⟩
    intro v hv
    by_cases hvb : v=b
    · subst v
      simp only [SearchState.routes, lookupRoute, if_pos rfl]
      obtain ⟨hsk,hbound,hdiv,hsupp,hlen⟩ := hi.2 a hr.1
      refine ⟨skew_addEdge hsk a b, bounded_addEdge hbound hab hr.2.2 (hsupp a b (Or.inr hr.2.1)), ?_, ?_, ?_⟩
      · intro v
        change divergence (addEdge (applyRoute f (st.routes a)) a b) v = _
        rw [divergence_addEdge, hdiv]
        ring
      · intro u v huv
        have huu : u ∉ st.seen ∨ v ∉ st.seen := by
          rcases huv with h | h
          · exact Or.inl (fun hu => h (mem_insert_of_mem hu))
          · exact Or.inr (fun hv => h (mem_insert_of_mem hv))
        have hd : delta a b u v = 0 := by
          rcases huv with hu | hv
          · have hneA : u ≠ a := by intro h; exact hu (h ▸ mem_insert_of_mem hr.1)
            have hneB : u ≠ b := by intro h; exact hu (h ▸ mem_insert_self _ _)
            simp [delta,hneA,hneB]
          · have hneA : v ≠ a := by intro h; exact hv (h ▸ mem_insert_of_mem hr.1)
            have hneB : v ≠ b := by intro h; exact hv (h ▸ mem_insert_self _ _)
            simp [delta,hneA,hneB]
        change applyRoute f (st.routes a) u v + delta a b u v = f u v
        rw [hsupp u v huu, hd, add_zero]
      · change (st.routes a).length + 1 + 1 ≤ (insert b st.seen).card
        rw [hcard]
        omega
    · have hvs : v ∈ st.seen := (mem_insert.mp hv).resolve_left hvb
      simp only [SearchState.routes, lookupRoute, if_neg hvb]
      obtain ⟨hsk,hbound,hdiv,hsupp,hlen⟩ := hi.2 v hvs
      refine ⟨hsk,hbound,hdiv,?_,?_⟩
      · intro u w huw
        apply hsupp u w
        exact huw.imp (fun h hu => h (mem_insert_of_mem hu)) (fun h hw => h (mem_insert_of_mem hw))
      · change (lookupRoute st.table v).length + 1 ≤ st.seen.card at hlen
        rw [hcard]
        omega

lemma search_invariant {cap : V → V → ℕ} {f : Matrix V} (s : V)
    (hsk : Skew f) (hb : Bounded cap f) (k : ℕ) :
    SearchInvariant cap f s (search cap f s k) := by
  induction k with
  | zero =>
    refine ⟨by simp [search], ?_⟩
    intro a ha
    have ha' : a=s := by simpa [search] using ha
    subst a
    refine ⟨hsk,hb,?_,?_,?_⟩
    · intro v
      simp [search,SearchState.routes,lookupRoute,applyRoute]
    · intro u v _
      rfl
    · simp [search,SearchState.routes,lookupRoute]
  | succ k ih => exact searchStep_invariant ih

lemma search_closed_or_card (cap : V → V → ℕ) (f : Matrix V) (s : V) (k : ℕ) :
    Closed cap f (search cap f s k).seen ∨ k+1 ≤ (search cap f s k).seen.card := by
  induction k with
  | zero => exact Or.inr (by simp [search])
  | succ k ih =>
    rw [search]
    cases he : frontier cap f (search cap f s k).seen with
    | none =>
      simp only [searchStep,he]
      exact Or.inl ((frontier_none_iff _ _ _).mp he)
    | some e =>
      obtain ⟨a,b⟩ := e
      simp only [searchStep,he]
      have hr := frontier_some he
      have hcard := card_insert_of_notMem hr.2.1
      have hn : ¬ Closed cap f (search cap f s k).seen := by
        intro hc
        rw [(frontier_none_iff _ _ _).mpr hc] at he
        contradiction
      exact Or.inr (by simpa [hcard] using Nat.add_le_add_right (ih.resolve_left hn) 1)

lemma search_closed (cap : V → V → ℕ) (f : Matrix V) (s : V) :
    Closed cap f (search cap f s (Fintype.card V)).seen := by
  rcases search_closed_or_card cap f s (Fintype.card V) with h | h
  · exact h
  · have hc := (search cap f s (Fintype.card V)).seen.card_le_univ
    omega

lemma internal_sum_zero {f : Matrix V} (hf : Skew f) (S : Finset V) :
    (∑ u ∈ S, ∑ v ∈ S, f u v) = 0 := by
  have h : (∑ u ∈ S, ∑ v ∈ S, f u v) = -(∑ u ∈ S, ∑ v ∈ S, f u v) := by
    calc
      _ = ∑ u ∈ S, ∑ v ∈ S, -f v u := by
        apply sum_congr rfl
        intro u _
        apply sum_congr rfl
        intro v _
        exact hf u v
      _ = -(∑ v ∈ S, ∑ u ∈ S, f v u) := by rw [sum_comm]; simp
  omega

lemma cut_balance {f : Matrix V} (hf : Skew f) (S : Finset V) :
    (∑ u ∈ S, divergence f u) = ∑ u ∈ S, ∑ v ∈ Sᶜ, f u v := by
  unfold divergence
  conv_lhs => arg 2; ext u; rw [← sum_add_sum_compl S (f u)]
  rw [sum_add_distrib, internal_sum_zero hf, zero_add]

lemma cut_value {cap : V → V → ℕ} {s t : V} {f : Matrix V}
    (hf : Valid cap s t f) (S : Finset V) (hs : s ∈ S) (ht : t ∉ S) :
    (∑ u ∈ S, ∑ v ∈ Sᶜ, f u v) = divergence f s := by
  rw [← cut_balance hf.1]
  apply sum_eq_single s
  · intro u hu hus
    exact hf.2.2 u hus (fun hut => ht (hut ▸ hu))
  · intro h
    exact (h hs).elim

/-- A closed residual cut prevents any feasible integral flow from having a
larger value. The witness is an ordinary valid flow, not a path oracle. -/
lemma closed_dominates {cap : V → V → ℕ} {s t : V} {f g : Matrix V}
    (hf : Valid cap s t f) (hg : Valid cap s t g) (S : Finset V)
    (hs : s ∈ S) (ht : t ∉ S) (hc : Closed cap f S) :
    divergence g s ≤ divergence f s := by
  rw [← cut_value hg S hs ht, ← cut_value hf S hs ht]
  apply sum_le_sum
  intro u hu
  apply sum_le_sum
  intro v hv
  have hv' : v ∉ S := mem_compl.mp hv
  exact (hg.2.1 u v).trans (hc u hu v hv')

/-- Explicit unit augmenting step: compute the finite residual search and apply
its stored route, or return the unchanged flow when the sink is unreachable. -/
def improve (cap : V → V → ℕ) (s t : V) (f : Matrix V) : Matrix V :=
  let st := search cap f s (Fintype.card V)
  if t ∈ st.seen then applyRoute f (st.routes t) else f

lemma improve_valid_value {cap : V → V → ℕ} {s t : V} {f g : Matrix V}
    (hst : s ≠ t) (hf : Valid cap s t f) (hg : Valid cap s t g)
    (hlt : divergence f s < divergence g s) :
    Valid cap s t (improve cap s t f) ∧
      divergence (improve cap s t f) s = divergence f s + 1 := by
  let st := search cap f s (Fintype.card V)
  have hi := search_invariant s hf.1 hf.2.1 (Fintype.card V)
  have ht : t ∈ st.seen := by
    by_contra hnot
    have hc := closed_dominates hf hg st.seen hi.1 hnot (search_closed cap f s)
    omega
  obtain ⟨hsk,hbound,hdiv,_,_⟩ := hi.2 t ht
  have heq : improve cap s t f = applyRoute f (st.routes t) := if_pos ht
  rw [heq]
  refine ⟨⟨hsk,hbound,?_⟩,?_⟩
  · intro v hvs hvt
    rw [hdiv, if_neg hvs, if_neg hvt, hf.2.2 v hvs hvt]
    ring
  · rw [hdiv, if_pos rfl, if_neg hst]
    ring

/-- Computable integral augmentation from the zero flow. -/
def run (cap : V → V → ℕ) (s t : V) : ℕ → Matrix V
  | 0 => fun _ _ => 0
  | k+1 => improve cap s t (run cap s t k)

lemma zero_valid (cap : V → V → ℕ) (s t : V) : Valid cap s t (fun _ _ => 0) := by
  refine ⟨?_,?_,?_⟩
  · intro u v; simp
  · intro u v; positivity
  · intro v _ _; simp [divergence]

/-- From any proved feasible flow of integral value R, the explicit algorithm
constructs a flow of value R in exactly R unit augmentations from zero. -/
theorem run_correct {cap : V → V → ℕ} {s t : V} {g : Matrix V} (hst : s ≠ t)
    (hg : Valid cap s t g) (R : ℕ) (hR : divergence g s = R) :
    ∀ k ≤ R, Valid cap s t (run cap s t k) ∧ divergence (run cap s t k) s = k := by
  intro k hk
  induction k with
  | zero => exact ⟨zero_valid cap s t, by simp [run,divergence]⟩
  | succ k ih =>
    obtain ⟨hv,hval⟩ := ih (by omega)
    have hlt : divergence (run cap s t k) s < divergence g s := by rw [hval,hR]; exact_mod_cast hk
    obtain ⟨hvalid,hvalue⟩ := improve_valid_value hst hv hg hlt
    exact ⟨hvalid, by simpa only [run, hval, Nat.cast_add, Nat.cast_one] using hvalue⟩
end SemidegreeExt.FlowAlgorithm
