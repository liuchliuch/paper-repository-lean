import Paper20.Bounds
import Mathlib

/-! Concrete admissibility and the palindromic witnesses of Lemma 2.2.
No field assumes that the witnesses are admissible. The elementary argument
works for every family of involutions with all stays allowed at the initial
state. The final specialization uses adjacent transpositions and the actual
descent test at the reverse permutation. -/
namespace Paper20.BraidWalk
open Finset BigOperators

variable {I S : Type*}

/-- State reached by the decorated word (`true` means stay). -/
def endpoint (move : I → S → S) : List (I × Bool) → S → S
  | [], s => s
  | (i,b) :: xs, s => endpoint move xs (if b then s else move i s)

/-- Every stay must be a descent at its current state. -/
def permitted (move : I → S → S) (allowed : I → S → Prop) : List (I × Bool) → S → Prop
  | [], _ => True
  | (i,b) :: xs, s =>
      (b = true → allowed i s) ∧ permitted move allowed xs (if b then s else move i s)

/-- The complete admissibility condition, including the final state. -/
def closed (move : I → S → S) (allowed : I → S → Prop)
    (top : S) (xs : List (I × Bool)) : Prop :=
  permitted move allowed xs top ∧ endpoint move xs top = top

lemma endpoint_append (move : I → S → S) (xs ys : List (I × Bool)) (s : S) :
    endpoint move (xs++ys) s = endpoint move ys (endpoint move xs s) := by
  induction xs generalizing s with
  | nil => rfl
  | cons a xs ih => cases a; simpa only [endpoint, List.cons_append] using ih _

lemma permitted_append (move : I → S → S) (allowed : I → S → Prop)
    (xs ys : List (I × Bool)) (s : S) :
    permitted move allowed (xs++ys) s ↔
      permitted move allowed xs s ∧ permitted move allowed ys (endpoint move xs s) := by
  induction xs generalizing s with
  | nil => simp [permitted, endpoint]
  | cons a xs ih => cases a; simp only [List.cons_append, permitted, endpoint, ih, and_assoc]

/-- Moving along a word and its reversal returns to the original state. -/
lemma moving_palindrome (move : I → S → S) (hinv : ∀ i, Function.Involutive (move i))
    (Q : List I) (s : S) :
    endpoint move ((Q++Q.reverse).map (fun i => (i,false))) s = s := by
  induction Q generalizing s with
  | nil => rfl
  | cons i Q ih =>
    have he : (((i::Q)++(i::Q).reverse).map (fun i => (i,false))) =
        (i,false) :: ((Q++Q.reverse).map (fun i => (i,false)) ++ [(i,false)]) := by
      simp [List.reverse_cons, List.map_append, List.append_assoc]
    rw [he]
    change endpoint move ((Q++Q.reverse).map (fun i => (i,false)) ++ [(i,false)]) (move i s) = s
    rw [endpoint_append, ih]
    simpa [endpoint] using hinv i s

lemma permitted_moves (move : I → S → S) (allowed : I → S → Prop)
    (Q : List I) (s : S) :
    permitted move allowed (Q.map (fun i => (i,false))) s := by
  induction Q generalizing s with
  | nil => trivial
  | cons i Q ih => simpa [permitted] using ih (move i s)

lemma stays_endpoint (move : I → S → S) (Q : List I) (s : S) :
    endpoint move (Q.map (fun i => (i,true))) s = s := by
  induction Q with
  | nil => rfl
  | cons i Q ih => simpa [endpoint] using ih

lemma permitted_stays (move : I → S → S) (allowed : I → S → Prop)
    (top : S) (htop : ∀ i, allowed i top) (Q : List I) :
    permitted move allowed (Q.map (fun i => (i,true))) top := by
  induction Q with
  | nil => trivial
  | cons i Q ih => simp [permitted, htop, ih]

/-- The witness constructed in the source proof: initial and final stays,
with a middle word followed by its reversal. -/
def witness (Q : List I) (h : ℕ) : List (I × Bool) :=
  (Q.take h).map (fun i => (i,true)) ++
    (Q.drop h ++ (Q.drop h).reverse).map (fun i => (i,false)) ++
      (Q.take h).reverse.map (fun i => (i,true))

/-- Admissibility is derived from moves and descents. -/
theorem witness_closed (move : I → S → S) (hinv : ∀ i, Function.Involutive (move i))
    (allowed : I → S → Prop) (top : S) (htop : ∀ i, allowed i top)
    (Q : List I) (h : ℕ) : closed move allowed top (witness Q h) := by
  unfold closed witness
  constructor
  · rw [permitted_append, permitted_append, endpoint_append,
      stays_endpoint, moving_palindrome move hinv]
    exact ⟨⟨permitted_stays move allowed top htop _, permitted_moves move allowed _ top⟩,
      permitted_stays move allowed top htop _⟩
  · rw [endpoint_append, endpoint_append, stays_endpoint,
      moving_palindrome move hinv, stays_endpoint]

lemma count_snd_map (Q : List I) (b : Bool) :
    ((Q.map (fun i => (i,b))).map Prod.snd).count true =
      if b then Q.length else 0 := by
  induction Q with
  | nil => cases b <;> rfl
  | cons i Q ih => cases b <;> simpa using ih

/-- Exactly `2h` stays in the admissible witness. -/
theorem witness_stays (Q : List I) (h : ℕ) (hh : h ≤ Q.length) :
    ((witness Q h).map Prod.snd).count true = 2*h := by
  simp only [witness, List.map_append, List.count_append, count_snd_map,
    Bool.true_eq, Bool.false_eq_true, ↓reduceIte, List.length_reverse,
    List.length_take, min_eq_left hh]
  omega

/-- The underlying word is the actual palindrome, independent of the stays. -/
theorem witness_word (Q : List I) (h : ℕ) :
    (witness Q h).map Prod.fst = Q++Q.reverse := by
  have hm (l : List I) (b : Bool) : (l.map (fun i => (i,b))).map Prod.fst = l := by
    induction l with
    | nil => rfl
    | cons i l ih => simpa using ih
  simp only [witness, List.map_append, hm]
  calc
    _ = (Q.take h ++ Q.drop h) ++ (Q.take h ++ Q.drop h).reverse := by
      rw [List.reverse_append]
      simp only [List.append_assoc]
    _ = _ := by rw [List.take_append_drop]

lemma bool_count_sum (l : List Bool) :
    l.count true = (l.map (fun b => if b then (1:ℕ) else 0)).sum := by
  induction l with
  | nil => rfl
  | cons b l ih => cases b <;> simp [ih, Nat.add_comm]

/-- The list and finite-function representations count the same stays. -/
lemma nStays_ofFn {m : ℕ} (w : Walks.Walk m) :
    (List.ofFn w).count true = Walks.nStays w := by
  rw [bool_count_sum]
  simp only [List.map_ofFn, List.sum_ofFn]
  simp [Walks.nStays, Walks.staySet, Finset.sum_boole]

/-- Admissible walks for a fixed generator word. -/
def admissible (move : I → S → S) (allowed : I → S → Prop) (top : S)
    (word : List I) (w : Walks.Walk word.length) : Prop :=
  closed move allowed top (word.zip (List.ofFn w))

/-- An admissible palindrome with exactly `2h` stays exists. -/
theorem exists_admissible (move : I → S → S)
    (hinv : ∀ i, Function.Involutive (move i))
    (allowed : I → S → Prop) (top : S) (htop : ∀ i, allowed i top)
    (Q : List I) (h : ℕ) (hh : h ≤ Q.length) :
    ∃ w : Walks.Walk (Q++Q.reverse).length,
      admissible move allowed top (Q++Q.reverse) w ∧ Walks.nStays w = 2*h := by
  let steps := witness Q h
  let choices := steps.map Prod.snd
  have hword : steps.map Prod.fst = Q++Q.reverse := witness_word Q h
  have hlen : choices.length = (Q++Q.reverse).length := by
    simpa only [choices, List.length_map] using congrArg List.length hword
  let w : Walks.Walk (Q++Q.reverse).length :=
    fun i => choices.get ⟨i.val, by rw [hlen]; exact i.isLt⟩
  have hlist : List.ofFn w = choices := by
    apply List.ext_getElem
    · simp [hlen]
    · intro i hi hi'
      simp [w]
  refine ⟨w, ?_, ?_⟩
  · unfold admissible
    rw [hlist, ← hword]
    have hz : (steps.map Prod.fst).zip (steps.map Prod.snd) = steps := by
      rw [List.zip_map']
      simp
    rw [show choices = steps.map Prod.snd from rfl, hz]
    exact witness_closed move hinv allowed top htop Q h
  · rw [← nStays_ofFn, hlist]
    exact witness_stays Q h hh

/-- The complete lower and upper bounds for concrete admissibility, with
no premise asserting admissibility of the palindromic witnesses. -/
theorem concrete_bounds (move : I → S → S)
    (hinv : ∀ i, Function.Involutive (move i))
    (allowed : I → S → Prop) (top : S) (htop : ∀ i, allowed i top)
    (Q : List I) (h : ℕ) (hh : h ≤ Q.length) :
    1 ≤ Walks.admissibleCount (admissible move allowed top (Q++Q.reverse)) h ∧
      Walks.admissibleCount (admissible move allowed top (Q++Q.reverse)) h ≤
        Nat.choose (2*Q.length) (2*h) := by
  constructor
  · obtain ⟨w, hw, hs⟩ := exists_admissible move hinv allowed top htop Q h hh
    haveI : Nonempty {w : Walks.Walk (Q++Q.reverse).length //
        admissible move allowed top (Q++Q.reverse) w ∧ Walks.nStays w = 2*h} :=
      ⟨⟨w, hw, hs⟩⟩
    exact Nat.succ_le_of_lt Nat.card_pos
  · simpa [List.length_append, List.length_reverse, two_mul] using
      Walks.admissibleCount_le (admissible move allowed top (Q++Q.reverse)) h

/-- Left multiplication by the adjacent transposition. -/
def adjacentMove {r : ℕ} (i : Fin (r-1)) (p : Equiv.Perm (Fin r)) : Equiv.Perm (Fin r) :=
  Equiv.swap ⟨i.val, by omega⟩ ⟨i.val+1, by omega⟩ * p

/-- The descent condition for the standard Hecke basis action (6). -/
def descent {r : ℕ} (i : Fin (r-1)) (p : Equiv.Perm (Fin r)) : Prop :=
  (p.symm ⟨i.val+1, by omega⟩).val < (p.symm ⟨i.val, by omega⟩).val

lemma adjacentMove_involutive {r : ℕ} (i : Fin (r-1)) :
    Function.Involutive (adjacentMove i) := by
  intro p
  simp [adjacentMove, ← mul_assoc]

lemma reverse_descent {r : ℕ} (i : Fin (r-1)) : descent i Fin.revPerm := by
  unfold descent
  rw [Fin.revPerm_symm]
  change (Fin.rev (⟨i.val+1, by omega⟩ : Fin r)).val <
    (Fin.rev (⟨i.val, by omega⟩ : Fin r)).val
  simp only [Fin.val_rev]
  omega

/-- The required witnesses for any chosen half-twist word now follow with
no hypothesis asserting their admissibility. -/
theorem adjacent_witness_closed {r : ℕ} (Q : List (Fin (r-1))) (h : ℕ) :
    closed adjacentMove descent Fin.revPerm (witness Q h) :=
  witness_closed adjacentMove adjacentMove_involutive descent Fin.revPerm
    reverse_descent Q h

/-- A standard triangular positive half-twist word on `n+1` strands. -/
def deltaWord : (n : ℕ) → List (Fin n)
  | 0 => []
  | n+1 => (deltaWord n).map Fin.castSucc ++ List.ofFn (fun i : Fin (n+1) => i.rev)

lemma deltaWord_length (n : ℕ) : (deltaWord n).length = Nat.choose (n+1) 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [deltaWord, List.length_append, List.length_map, List.length_ofFn, ih]
    have hc := Nat.choose_succ_succ (n+1) 1
    change Nat.choose (n+1+1) 2 = Nat.choose (n+1) 1 + Nat.choose (n+1) 2 at hc
    rw [Nat.choose_one_right] at hc
    omega

/-- A word of length `k binom(r,2)` for `k` half twists. -/
def halfWord (r k : ℕ) : List (Fin (r-1)) :=
  (List.replicate k (deltaWord (r-1))).flatten

lemma halfWord_length (r k : ℕ) : (halfWord r k).length = deg r k := by
  have hd : (deltaWord (r-1)).length = Nat.choose r 2 := by
    cases r with
    | zero => rfl
    | succ r => simpa using deltaWord_length r
  simp [halfWord, List.length_flatten, List.map_replicate, List.sum_replicate, hd, deg]

/-- The concrete closed braid-walk count, as opposed to an arbitrary
predicate assumed to satisfy the lower bound. -/
noncomputable def walkCount (r k h : ℕ) : ℕ :=
  Walks.admissibleCount
    (admissible adjacentMove descent Fin.revPerm
      (halfWord r k ++ (halfWord r k).reverse)) h

/-- The full bounds of Lemma 2.2 for the concrete adjacent-transposition model. -/
theorem walk_bounds (r k h : ℕ) (hh : h ≤ deg r k) :
    1 ≤ walkCount r k h ∧ walkCount r k h ≤ Nat.choose (2*deg r k) (2*h) := by
  have hb := concrete_bounds adjacentMove adjacentMove_involutive descent Fin.revPerm
    reverse_descent (halfWord r k) h (by rwa [halfWord_length])
  simpa only [walkCount, halfWord_length] using hb

/-- Both endpoint counts are exactly one. -/
theorem walk_endpoints (r k : ℕ) : walkCount r k 0 = 1 ∧ walkCount r k (deg r k) = 1 := by
  have h0 := walk_bounds r k 0 (Nat.zero_le _)
  have hd := walk_bounds r k (deg r k) le_rfl
  simp only [Nat.mul_zero, Nat.choose_zero_right] at h0
  simp only [Nat.choose_self] at hd
  exact ⟨le_antisymm h0.2 h0.1, le_antisymm hd.2 hd.1⟩

end Paper20.BraidWalk
