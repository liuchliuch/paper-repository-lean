import Paper20.RContentVectorEvaluation
import Paper20.Certs.ACacheFast36.All

namespace Paper20.RContent36
open Polynomial Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def sumVectors {α : Type*} (xs : List α) (f : α → List ℤ) : List ℤ :=
  xs.foldr (fun x acc => IntegerPolynomial.add (f x) acc) []

lemma sumVectors_getD {α : Type*} (xs : List α) (f : α → List ℤ) (i : ℕ) :
    (sumVectors xs f).getD i 0=(xs.map (fun x => (f x).getD i 0)).sum := by
  induction xs with
  | nil => simp [sumVectors]
  | cons x xs ih =>
    rw [sumVectors,List.foldr_cons,integer_add_getD]
    change (f x).getD i 0+(sumVectors xs f).getD i 0=_
    rw [ih]
    rfl

def fastRowVector (p : ℕ × List ℤ) (h : ℕ) : List ℤ :=
  sumVectors (List.range (h+1)) (fun j =>
    IntegerPolynomial.scale (p.2.getD (h-j) 0*(FastQ36.cofactor h j:ℤ))
      (Cert.ACacheFast36.aCached p.1 j))

def evaluateFastVector (s : State) (h : ℕ) : List ℤ := sumVectors s (fun p => fastRowVector p h)

lemma fastRowVector_getD (p : ℕ × List ℤ) (hc : p.1 ≤ 630)
    (h i : ℕ) (hh : h ≤ 22) :
    (fastRowVector p h).getD i 0=
      ∑ j ∈ range (h+1), p.2.getD (h-j) 0*aWeight h i j p.1 := by
  rw [fastRowVector,sumVectors_getD,sum_map_range_int]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j ≤ 22 := by have := Finset.mem_range.mp hj; omega
  rw [integer_scale_getD,← Cert.ACacheFast36.aCached_correct p.1 j hc hj']
  unfold aWeight
  ring

/-- Fast row caching and whole-vector accumulation preserve every actual
coefficient of the independent complete partition reconstruction. -/
theorem evaluateFastVector_correct (s : State) (hb : ∀ p ∈ s, p.1 ≤ 630)
    (h i : ℕ) (hh : h ≤ 22) :
    (evaluateFastVector s h).getD i 0=evaluate s h i := by
  rw [evaluateFastVector,sumVectors_getD,evaluate,sum_map_range_int,range_sum_list_comm]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  exact fastRowVector_getD p (hb p hp) h i hh

theorem evaluateFastVector_scaled (s : State) (hs : Correct root s)
    (hb : ∀ p ∈ s, p.1 ≤ 630) (h i : ℕ) (hh : h ≤ 22) :
    ((evaluateFastVector s h).getD i 0:ℚ)=
      (FastQ36.denominator h:ℚ)*((36:ℕ).factorial:ℚ)*cget (Qcoeff 36 h) i := by
  rw [evaluateFastVector_correct s hb h i hh]
  exact evaluate_scaled s hs hb h i hh

end
end Paper20.RContent36
