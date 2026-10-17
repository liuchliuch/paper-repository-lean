import Paper20.HeckeMatrices
import Paper20.HalfTwistWord

namespace Paper20.HalfTwistMatrix
open Polynomial Matrix Paper20.BraidWalk Paper20.HeckeOperators Paper20.HeckeMatrices
open Paper20.HalfTwistWord
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Generic
variable {S R : Type*} [Fintype S] [DecidableEq S] [CommRing R]

lemma down_transpose (g : ℕ → Matrix S S R) (hg : ∀ i, (g i).transpose=g i) (n : ℕ) :
    (down g n).transpose=up g n := by
  induction n with
  | zero => simp [down,up]
  | succ n ih => rw [down_succ,Matrix.transpose_mul,hg,ih,up_succ]

/-- The explicit triangular half-twist product is symmetric. The only
word changes used are the actual distant-generator commutations. -/
theorem triangle_transpose (g : ℕ → Matrix S S R)
    (hg : ∀ i, (g i).transpose=g i)
    (hfar : ∀ i j, i+1 < j → Commute (g i) (g j)) (n : ℕ) :
    (triangle g n).transpose=triangle g n := by
  induction n with
  | zero => simp [triangle,word]
  | succ n ih =>
    rw [triangle_succ,Matrix.transpose_mul,down_transpose g hg,ih]
    simpa only [triangle_succ] using (triangle_mirror g hfar n).symm

end Generic

def generator (r j : ℕ) : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℤ[X] :=
  if h : j < r-1 then T r ⟨j,h⟩ else 1

lemma generator_fin (r : ℕ) (i : Fin (r-1)) : generator r i.val=T r i := by
  simp only [generator,dif_pos i.isLt]

lemma generator_far (r i j : ℕ) (hij : i+1 < j) : Commute (generator r i) (generator r j) := by
  by_cases hi : i < r-1 <;> by_cases hj : j < r-1
  · change generator r i*generator r j=generator r j*generator r i
    simp only [generator,dif_pos hi,dif_pos hj]
    exact T_commute r ⟨i,hi⟩ ⟨j,hj⟩ (Or.inl hij)
  · simp [generator,hi,hj]
  · simp [generator,hi,hj]
  · simp [generator,hi,hj]

lemma generator_transpose (r j : ℕ) : (generator r j).transpose=generator r j := by
  by_cases hj : j < r-1
  · rw [generator,dif_pos hj]
    exact generatorMatrix_symmetric _ _ (adjacentMove_involutive ⟨j,hj⟩) Polynomial.X
  · simp [generator,hj]

def halfTwist (r : ℕ) : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℤ[X] :=
  wordMatrix adjacentMove descent Polynomial.X (deltaWord (r-1))

lemma halfTwist_eq_triangle (r : ℕ) : halfTwist r=triangle (generator r) (r-1) := by
  rw [triangle,← deltaWord_values,List.map_map]
  unfold halfTwist wordMatrix
  apply congrArg List.prod
  apply List.map_congr_left
  intro i hi
  exact (generator_fin r i).symm

theorem halfTwist_transpose (r : ℕ) : (halfTwist r).transpose=halfTwist r := by
  rw [halfTwist_eq_triangle]
  exact triangle_transpose _ (generator_transpose r) (generator_far r) _

lemma wordMatrix_halfWord (r k : ℕ) :
    wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) (halfWord r k)=halfTwist r^k := by
  induction k with
  | zero => simp [halfWord,wordMatrix]
  | succ k ih =>
    have hw : halfWord r (k+1)=deltaWord (r-1)++halfWord r k := by
      simp [halfWord,List.replicate_succ]
    rw [hw,wordMatrix_append,ih,pow_succ']
    rfl

/-- The palindrome used by the actual closed walks is the k-th full
half-twist square in the same concrete Hecke representation. -/
theorem wordMatrix_palindrome (r k : ℕ) :
    wordMatrix adjacentMove descent (Polynomial.X:ℤ[X])
      (halfWord r k++(halfWord r k).reverse)=halfTwist r^(2*k) := by
  rw [wordMatrix_append,wordMatrix_reverse adjacentMove descent adjacentMove_involutive,
    wordMatrix_halfWord,Matrix.transpose_pow,halfTwist_transpose,← pow_add]
  congr 1
  omega

def fullTwist (r : ℕ) : Matrix (Equiv.Perm (Fin r)) (Equiv.Perm (Fin r)) ℤ[X] :=
  halfTwist r^2

theorem fullTwist_diagonal_coeff (r k h : ℕ) :
    ((fullTwist r^k) Fin.revPerm Fin.revPerm).coeff (2*h)=(walkCount r k h:ℤ) := by
  rw [fullTwist,← pow_mul,← wordMatrix_palindrome]
  exact halfWord_diagonal_coeff r k h

end
end Paper20.HalfTwistMatrix
