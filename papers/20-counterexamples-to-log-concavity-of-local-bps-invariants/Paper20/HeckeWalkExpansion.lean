import Paper20.HeckeOperators

namespace Paper20.HeckeWalkExpansion
open Polynomial Paper20.BraidWalk Paper20.HeckeOperators
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable
variable {I S R : Type*} [CommRing R]

/-- Successive standard-basis Hecke actions along the given word. -/
def wordAction (move : I → S → S) (allowed : I → S → Prop)
    (z : R) : List I → (S → R) → S → R
  | [], f => f
  | i::word, f => operator (move i) (allowed i) z (wordAction move allowed z word f)

def delta (top s : S) : R := if s=top then 1 else 0

def term (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (word : List I) (w : Walks.Walk word.length) (f : S → R) (s : S) : R :=
  if permitted move allowed (word.zip (List.ofFn w)) s then
    z^(Walks.nStays w)*f (endpoint move (word.zip (List.ofFn w)) s) else 0

lemma stays_cons (b : Bool) {n : ℕ} (w : Walks.Walk n) :
    Walks.nStays (Fin.cons b w) = (if b then 1 else 0)+Walks.nStays w := by
  rw [← nStays_ofFn,← nStays_ofFn]
  rw [List.ofFn_succ]
  cases b <;> simp [Nat.add_comm]

lemma term_false (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (i : I) (word : List I) (w : Walks.Walk word.length) (f : S → R) (s : S) :
    term move allowed z (i::word) (Fin.cons false w) f s =
      term move allowed z word w f (move i s) := by
  simp [term,List.ofFn_succ,permitted,endpoint,stays_cons]

lemma term_true (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (i : I) (word : List I) (w : Walks.Walk word.length) (f : S → R) (s : S) :
    term move allowed z (i::word) (Fin.cons true w) f s =
      if allowed i s then z*term move allowed z word w f s else 0 := by
  by_cases ha : allowed i s
  · simp only [term,List.ofFn_succ,List.zip_cons_cons,permitted,endpoint,
      Fin.cons_zero,Fin.cons_succ,stays_cons,Bool.true_eq,↓reduceIte,true_implies,ha,true_and]
    split_ifs <;> simp_all only [pow_add,pow_one,mul_zero] <;> ring
  · simp [term,List.ofFn_succ,permitted,ha]

/-- Exact expansion of the genuine Hecke action over every stay/move
choice, retaining both admissibility and the actual terminal permutation. -/
theorem wordAction_eq_sum (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (word : List I) (f : S → R) (s : S) :
    wordAction move allowed z word f s =
      ∑ w : Walks.Walk word.length, term move allowed z word w f s := by
  classical
  induction word generalizing s with
  | nil => simp [wordAction,term,Walks.nStays,Walks.staySet,permitted,endpoint]
  | cons i word ih =>
    have he := Fintype.sum_equiv (Fin.consEquiv (fun _ : Fin (word.length+1) => Bool))
      (fun p : Bool × Walks.Walk word.length =>
        term move allowed z (i::word) (Fin.cons p.1 p.2) f s)
      (fun w : Walks.Walk (i::word).length => term move allowed z (i::word) w f s)
      (by intro p; rfl)
    calc
      _ = ∑ p : Bool × Walks.Walk word.length,
          term move allowed z (i::word) (Fin.cons p.1 p.2) f s := by
        rw [Fintype.sum_prod_type]
        simp only [Fintype.sum_bool,term_false,term_true]
        rw [wordAction,operator,ih,ih]
        by_cases ha : allowed i s
        · simp only [ha,↓reduceIte,Finset.mul_sum]
          ring
        · simp [ha]
      _ = _ := he

/-- A delta function selects exactly the closed walks. -/
theorem wordAction_closed (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (word : List I) (top : S) :
    wordAction move allowed z word (delta top) top =
      ∑ w : Walks.Walk word.length,
        if admissible move allowed top word w then z^(Walks.nStays w) else 0 := by
  rw [wordAction_eq_sum]
  apply Finset.sum_congr rfl
  intro w hw
  unfold term admissible closed delta
  split_ifs <;> simp_all

/-- The coefficient of the standard-basis closed-walk polynomial is the
actual cardinality of the admissible walks, not an imposed trace formula. -/
theorem wordAction_coeff (move : I → S → S) (allowed : I → S → Prop)
    (word : List I) (top : S) (h : ℕ) :
    (wordAction move allowed (Polynomial.X : ℤ[X]) word
      (delta top) top).coeff (2*h) =
        (Walks.admissibleCount (admissible move allowed top word) h:ℤ) := by
  classical
  rw [wordAction_closed,Polynomial.finset_sum_coeff]
  unfold Walks.admissibleCount
  rw [Nat.card_eq_fintype_card,Fintype.card_subtype,Finset.card_eq_sum_ones]
  push_cast
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro w hw
  by_cases ha : admissible move allowed top word w <;>
    simp [ha,Polynomial.coeff_X_pow,eq_comm]

/-- The polynomial is built from the actual adjacent-permutation Hecke
operators and the exact palindromic half-twist word used by the witnesses. -/
def closedHeckePolynomial (r k : ℕ) : ℤ[X] := by
  classical
  exact wordAction adjacentMove descent Polynomial.X
    (halfWord r k++(halfWord r k).reverse)
    (delta Fin.revPerm) Fin.revPerm

theorem closedHeckePolynomial_coeff (r k h : ℕ) :
    (closedHeckePolynomial r k).coeff (2*h) = (walkCount r k h:ℤ) :=
  by
    simpa only [closedHeckePolynomial,walkCount] using
      wordAction_coeff adjacentMove descent (halfWord r k++(halfWord r k).reverse)
        Fin.revPerm h

theorem closedHeckePolynomial_bounds (r k h : ℕ) (hh : h ≤ deg r k) :
    1 ≤ (closedHeckePolynomial r k).coeff (2*h) ∧
      (closedHeckePolynomial r k).coeff (2*h) ≤ (Nat.choose (2*deg r k) (2*h):ℤ) := by
  rw [closedHeckePolynomial_coeff]
  exact_mod_cast walk_bounds r k h hh

end
end Paper20.HeckeWalkExpansion
