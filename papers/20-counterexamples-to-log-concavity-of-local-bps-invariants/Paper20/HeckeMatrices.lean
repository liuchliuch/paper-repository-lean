import Paper20.HeckeRelations
import Paper20.HeckeBPSPolynomial

namespace Paper20.HeckeMatrices
open Polynomial Matrix Paper20.BraidWalk Paper20.HeckeOperators Paper20.HeckeWalkExpansion
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Generic
variable {I S R : Type*} [Fintype S] [DecidableEq S] [CommRing R]

/-- Matrix multiplication is exactly the actual move/descent operator. -/
theorem generator_mulVec (move : S → S) (desc : S → Prop) (z : R)
    (f : S → R) :
    (generatorMatrix move desc z).mulVec f=operator move desc z f := by
  funext s
  by_cases hs : desc s <;>
    simp [generatorMatrix,operator,Matrix.mulVec,dotProduct,add_mul,
      Finset.sum_add_distrib,hs,eq_comm]

def wordMatrix (move : I → S → S) (allowed : I → S → Prop)
    (z : R) (word : List I) : Matrix S S R :=
  (word.map (fun i => generatorMatrix (move i) (allowed i) z)).prod

lemma wordMatrix_nil (move : I → S → S) (allowed : I → S → Prop) (z : R) :
    wordMatrix move allowed z []=1 := rfl

lemma wordMatrix_cons (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (i : I) (word : List I) :
    wordMatrix move allowed z (i::word)=
      generatorMatrix (move i) (allowed i) z*wordMatrix move allowed z word := rfl

lemma wordMatrix_append (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (u v : List I) :
    wordMatrix move allowed z (u++v)=wordMatrix move allowed z u*wordMatrix move allowed z v := by
  simp only [wordMatrix,List.map_append,List.prod_append]

theorem wordMatrix_mulVec (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (word : List I) (f : S → R) :
    (wordMatrix move allowed z word).mulVec f=wordAction move allowed z word f := by
  induction word with
  | nil => simp [wordMatrix,wordAction]
  | cons i word ih =>
    rw [wordMatrix_cons,← Matrix.mulVec_mulVec,ih,generator_mulVec,wordAction]

/-- Reversing a word transposes its actual standard-basis matrix. -/
theorem wordMatrix_reverse (move : I → S → S) (allowed : I → S → Prop)
    (hinv : ∀ i, Function.Involutive (move i)) (z : R) (word : List I) :
    wordMatrix move allowed z word.reverse=(wordMatrix move allowed z word).transpose := by
  induction word with
  | nil => simp [wordMatrix]
  | cons i word ih =>
    rw [List.reverse_cons,wordMatrix_append,ih]
    simp only [wordMatrix_cons,wordMatrix_nil,mul_one,Matrix.transpose_mul,
      generatorMatrix_symmetric (move i) (allowed i) (hinv i) z]

lemma mulVec_delta (M : Matrix S S R) (t s : S) : M.mulVec (delta t) s=M s t := by
  classical
  simp [Matrix.mulVec,dotProduct,delta,mul_ite]

/-- The walk polynomial is a genuine diagonal matrix coefficient. -/
theorem wordMatrix_diagonal (move : I → S → S) (allowed : I → S → Prop) (z : R)
    (word : List I) (top : S) :
    (wordMatrix move allowed z word) top top=
      wordAction move allowed z word (delta top) top := by
  rw [← wordMatrix_mulVec,mulVec_delta]

lemma matrix_eq_of_mulVec (M N : Matrix S S R)
    (h : ∀ f : S → R, M.mulVec f=N.mulVec f) : M=N := by
  ext s t
  have he := congrFun (h (delta t)) s
  simpa only [mulVec_delta] using he

end Generic

/-- The actual standard-basis adjacent Hecke matrix over Z[z]. -/
def T (r : ℕ) (i : Fin (r-1)) : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℤ[X] :=
  generatorMatrix (adjacentMove i) (descent i) Polynomial.X

theorem T_quadratic (r : ℕ) (i : Fin (r-1)) :
    T r i*T r i=1+(Polynomial.X:ℤ[X]) • T r i := by
  apply matrix_eq_of_mulVec
  intro f
  funext p
  rw [← Matrix.mulVec_mulVec,Matrix.add_mulVec,Matrix.one_mulVec,Matrix.smul_mulVec]
  simp only [T,generator_mulVec,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  exact adjacent_quadratic i Polynomial.X f p

theorem T_braid (r : ℕ) (i j : Fin (r-1)) (hij : j.val=i.val+1) :
    T r i*T r j*T r i=T r j*T r i*T r j := by
  apply matrix_eq_of_mulVec
  intro f
  funext p
  simp only [← Matrix.mulVec_mulVec,T,generator_mulVec]
  exact adjacent_braid i j hij Polynomial.X f p

theorem T_commute (r : ℕ) (i j : Fin (r-1))
    (hij : i.val+1 < j.val ∨ j.val+1 < i.val) : T r i*T r j=T r j*T r i := by
  apply matrix_eq_of_mulVec
  intro f
  funext p
  simp only [← Matrix.mulVec_mulVec,T,generator_mulVec]
  exact adjacent_commute i j hij Polynomial.X f p

/-- The coefficient of the actual full palindromic word matrix equals the
original concrete admissible-walk count, with no trace hypothesis. -/
theorem halfWord_diagonal_coeff (r k h : ℕ) :
    ((wordMatrix adjacentMove descent (Polynomial.X:ℤ[X])
      (halfWord r k++(halfWord r k).reverse)) Fin.revPerm Fin.revPerm).coeff (2*h) =
        (walkCount r k h:ℤ) := by
  rw [wordMatrix_diagonal]
  exact closedHeckePolynomial_coeff r k h

end
end Paper20.HeckeMatrices
