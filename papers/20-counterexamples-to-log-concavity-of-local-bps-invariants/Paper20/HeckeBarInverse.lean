import Paper20.HeckeBar

namespace Paper20.HeckeBar
open Polynomial Matrix Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
open Paper20.HeckeOperators Paper20.BraidWalk Paper20.HeckeWalkExpansion
open Paper20.HalfTwistMatrix
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- Parameter negation conjugated by the actual longest-state permutation. -/
def conjugateBar (r : ℕ) : Mat r →+* Mat r where
  toFun A := J r*bar r A*J r
  map_zero' := by simp
  map_one' := by rw [map_one,mul_one,J_square]
  map_add' A B := by rw [map_add,mul_add,add_mul]
  map_mul' A B := by
    rw [map_mul]
    simp only [mul_assoc,← mul_assoc (J r) (J r),J_square,one_mul]

lemma conjugateBar_T (r : ℕ) (i : Fin (r-1)) :
    conjugateBar r (T r i)=inverseGenerator r i := J_bar_T_J r i

def inverseWord (r : ℕ) (w : List (Fin (r-1))) : Mat r :=
  (w.reverse.map (inverseGenerator r)).prod

lemma inverseWord_nil (r : ℕ) : inverseWord r []=1 := rfl
lemma inverseWord_cons (r : ℕ) (i : Fin (r-1)) (w : List (Fin (r-1))) :
    inverseWord r (i::w)=inverseWord r w*inverseGenerator r i := by
  simp [inverseWord,List.reverse_cons,List.prod_append]

lemma inverseWord_mul_word (r : ℕ) (w : List (Fin (r-1))) :
    inverseWord r w*wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w=1 := by
  induction w with
  | nil => simp [inverseWord,wordMatrix]
  | cons i w ih =>
    rw [inverseWord_cons,wordMatrix_cons]
    change (inverseWord r w*inverseGenerator r i)*
      (T r i*wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w)=1
    rw [mul_assoc,← mul_assoc (inverseGenerator r i),inverseGenerator_mul_T,one_mul,ih]

lemma word_mul_inverseWord (r : ℕ) (w : List (Fin (r-1))) :
    wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w*inverseWord r w=1 := by
  induction w with
  | nil => simp [inverseWord,wordMatrix]
  | cons i w ih =>
    rw [inverseWord_cons,wordMatrix_cons]
    change (T r i*wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w)*
      (inverseWord r w*inverseGenerator r i)=1
    rw [mul_assoc,← mul_assoc (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w),
      ih,one_mul,T_mul_inverseGenerator]

lemma conjugateBar_word (r : ℕ) (w : List (Fin (r-1))) :
    conjugateBar r (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w)=
      inverseWord r w.reverse := by
  induction w with
  | nil => simp [wordMatrix,inverseWord]
  | cons i w ih =>
    rw [wordMatrix_cons,map_mul]
    change conjugateBar r (T r i)*
      conjugateBar r (wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w)=_
    rw [conjugateBar_T,ih]
    simp [inverseWord]

lemma halfTwist_word_reverse (r : ℕ) :
    wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) (deltaWord (r-1)).reverse=halfTwist r := by
  rw [wordMatrix_reverse adjacentMove descent adjacentMove_involutive]
  exact halfTwist_transpose r

lemma conjugateBar_halfTwist (r : ℕ) :
    conjugateBar r (halfTwist r)=inverseWord r (deltaWord (r-1)) := by
  rw [← halfTwist_word_reverse,conjugateBar_word,List.reverse_reverse]

theorem conjugateBar_halfTwist_mul (r : ℕ) :
    conjugateBar r (halfTwist r)*halfTwist r=1 := by
  rw [conjugateBar_halfTwist]
  exact inverseWord_mul_word r _

theorem halfTwist_mul_conjugateBar (r : ℕ) :
    halfTwist r*conjugateBar r (halfTwist r)=1 := by
  rw [conjugateBar_halfTwist]
  exact word_mul_inverseWord r _

/-- The genuine bar/position-reversal involution sends the full twist to
its actual polynomial inverse. This is proved from explicit word inverses. -/
theorem conjugateBar_fullTwist_mul (r : ℕ) :
    conjugateBar r (fullTwist r)*fullTwist r=1 := by
  rw [fullTwist,map_pow]
  calc
    (conjugateBar r (halfTwist r))^2*(halfTwist r)^2=
        conjugateBar r (halfTwist r)*(conjugateBar r (halfTwist r)*halfTwist r)*halfTwist r := by
      simp only [pow_two,mul_assoc]
    _ = 1 := by rw [conjugateBar_halfTwist_mul,mul_one,conjugateBar_halfTwist_mul]

end
end Paper20.HeckeBar
