import Paper20.HeckeTraceDuality

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Paper20.BraidWalk Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion Paper20.HeckeSorting
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def invertVector (r : ℕ) (f : State r → ℤ[X]) : State r → ℤ[X] := fun p => f p.symm

def rightWordMatrix (r : ℕ) (word : List (Fin (r-1))) : Mat r := (word.map (rightT r)).prod

lemma rightWord_nil (r : ℕ) : rightWordMatrix r []=1 := rfl
lemma rightWord_cons (r : ℕ) (i : Fin (r-1)) (w : List (Fin (r-1))) :
    rightWordMatrix r (i::w)=rightT r i*rightWordMatrix r w := rfl
lemma rightWord_append (r : ℕ) (u v : List (Fin (r-1))) :
    rightWordMatrix r (u++v)=rightWordMatrix r u*rightWordMatrix r v := by
  simp [rightWordMatrix,List.prod_append]

lemma left_commute_rightWord (r : ℕ) (i : Fin (r-1)) (w : List (Fin (r-1))) :
    Commute (T r i) (rightWordMatrix r w) := by
  apply Commute.list_prod_right
  intro M hM
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hM
  exact left_right_commute r i j

lemma rightT_delta_one (r : ℕ) (i : Fin (r-1)) :
    (rightT r i).mulVec (delta (1 : State r))=(T r i).mulVec (delta (1 : State r)) := by
  funext s
  simpa only [mulVec_delta] using (column_one_equal r i s).symm

lemma rightWord_reverse_delta (r : ℕ) (w : List (Fin (r-1))) :
    (rightWordMatrix r w.reverse).mulVec (delta (1 : State r))=
      (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w).mulVec (delta (1 : State r)) := by
  induction w with
  | nil => simp [rightWordMatrix,wordMatrix]
  | cons i w ih =>
    rw [List.reverse_cons,rightWord_append,rightWord_cons,rightWord_nil,mul_one]
    calc
      _ = (rightWordMatrix r w.reverse).mulVec ((rightT r i).mulVec (delta (1 : State r))) := by
        rw [Matrix.mulVec_mulVec]
      _ = (rightWordMatrix r w.reverse).mulVec ((T r i).mulVec (delta (1 : State r))) := by
        rw [rightT_delta_one]
      _ = (rightWordMatrix r w.reverse*T r i).mulVec (delta (1 : State r)) := by
        rw [Matrix.mulVec_mulVec]
      _ = (T r i*rightWordMatrix r w.reverse).mulVec (delta (1 : State r)) := by
        rw [(left_commute_rightWord r i w.reverse).eq]
      _ = (T r i).mulVec ((rightWordMatrix r w.reverse).mulVec (delta (1 : State r))) := by
        rw [Matrix.mulVec_mulVec]
      _ = (T r i).mulVec ((wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w).mulVec
          (delta (1 : State r))) := by rw [ih]
      _ = _ := by rw [wordMatrix_cons,← Matrix.mulVec_mulVec]; rfl

lemma rightOperator_invertVector (r : ℕ) (i : Fin (r-1)) (f : State r → ℤ[X]) :
    operator (rightMove i) (rightDescent i) Polynomial.X (invertVector r f)=
      invertVector r (operator (adjacentMove i) (descent i) Polynomial.X f) := by
  funext p
  simp only [operator,invertVector,rightMove_symm,← rightDescent_eq i p]

lemma rightWord_invertVector (r : ℕ) (w : List (Fin (r-1))) (f : State r → ℤ[X]) :
    (rightWordMatrix r w).mulVec (invertVector r f)=
      invertVector r ((wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w).mulVec f) := by
  induction w with
  | nil => simp [rightWordMatrix,wordMatrix]
  | cons i w ih =>
    rw [rightWord_cons,← Matrix.mulVec_mulVec,ih,wordMatrix_cons,← Matrix.mulVec_mulVec]
    simp only [rightT,T,generator_mulVec]
    exact rightOperator_invertVector r i _

lemma invertVector_delta (r : ℕ) (p : State r) : invertVector r (delta p)=delta p.symm := by
  funext q
  have he : q.symm=p ↔ q=p.symm := by
    constructor
    · intro h; exact congrArg (fun a : State r => a.symm) h
    · intro h; rw [h]; rfl
  simp only [invertVector,delta,he]
  split_ifs <;> rfl

/-- Transpose and permutation inversion agree on the identity column of
every actual Hecke generator word. -/
theorem word_transpose_delta (r : ℕ) (w : List (Fin (r-1))) :
    ((wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w).transpose).mulVec
      (delta (1 : State r)) =
        invertVector r ((wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w).mulVec
          (delta (1 : State r))) := by
  rw [← wordMatrix_reverse adjacentMove descent adjacentMove_involutive]
  have he := rightWord_reverse_delta r w.reverse
  rw [List.reverse_reverse] at he
  rw [← he]
  have hi : invertVector r (delta (1 : State r))=delta (1 : State r) := invertVector_delta r 1
  rw [← hi,rightWord_invertVector,hi]

/-- Actual ascent words exist for every permutation, using the proved
strictly decreasing descent-sorting potential. -/
theorem exists_basis_word (r : ℕ) (p : State r) :
    ∃ w : List (Fin (r-1)),
      (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w).mulVec (delta (1 : State r))=delta p := by
  have aux : ∀ n : ℕ, ∀ p : State r, potential p=n →
      ∃ w : List (Fin (r-1)),
        (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w).mulVec (delta (1 : State r))=delta p := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro p hn
      by_cases hp : p=1
      · exact ⟨[],by simp [wordMatrix,hp]⟩
      · obtain ⟨i,hd⟩ := exists_descent p hp
        have hlt : potential (adjacentMove i p) < n := by
          rw [← hn]
          exact potential_descent_lt i p hd
        obtain ⟨w,hw⟩ := ih _ hlt (adjacentMove i p) rfl
        refine ⟨i::w,?_⟩
        rw [wordMatrix_cons,← Matrix.mulVec_mulVec,hw,generator_mulVec]
        have ha : ¬descent i (adjacentMove i p) := by
          rw [adjacent_descent_flip]
          exact not_not.mpr hd
        have he := operator_delta_ascent (adjacentMove i) (descent i)
          (adjacentMove_involutive i) (Polynomial.X:ℤ[X]) (adjacentMove i p) ha
        simpa only [adjacentMove_involutive i p] using he
  exact aux (potential p) p rfl

/-- The actual transpose anti-involution sends T_p to T_(p^-1), proved
using explicit ascent words, right commutation and actual faithfulness. -/
theorem basisMatrix_transpose (r : ℕ) (p : State r) :
    (basisMatrix r p).transpose=basisMatrix r p.symm := by
  obtain ⟨w,hw⟩ := exists_basis_word r p
  have hM : wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w=basisMatrix r p := by
    apply eq_of_identity_column r _ _ (wordMatrix_mem r w) (basisMatrix_mem r p)
    rw [hw,basisMatrix_delta]
  apply eq_of_identity_column r _ _ (transpose_mem r _ (basisMatrix_mem r p)) (basisMatrix_mem r p.symm)
  rw [← hM,word_transpose_delta,hw,invertVector_delta,basisMatrix_delta]

/-- The source's genuine dual-basis identity (10), now using actual
permutation inverse and the canonical trace of the free Hecke algebra. -/
theorem trace_basis_inverse (r : ℕ) (p q : State r) :
    trace r (basisMatrix r p*basisMatrix r q.symm)=if p=q then 1 else 0 := by
  rw [← basisMatrix_transpose r q]
  rw [trace_mul_comm r _ _ (basisMatrix_mem r p) (transpose_mem r _ (basisMatrix_mem r q)),
    trace_basis_duality]
  simp only [eq_comm]

end
end Paper20.HeckeTraceAlgebra
