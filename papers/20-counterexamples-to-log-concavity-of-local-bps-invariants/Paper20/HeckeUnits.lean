import Paper20.HeckeFullTwistCenter

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Paper20.HeckeMatrices Paper20.HalfTwistMatrix
open Paper20.HeckeWalkExpansion Paper20.BraidWalk
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def inverseGenerator (r : ℕ) (i : Fin (r-1)) : Mat r := T r i-(Polynomial.X:ℤ[X]) • 1

lemma T_mul_inverseGenerator (r : ℕ) (i : Fin (r-1)) : T r i*inverseGenerator r i=1 := by
  rw [inverseGenerator,mul_sub,T_quadratic,Matrix.mul_smul,mul_one]
  abel

lemma inverseGenerator_mul_T (r : ℕ) (i : Fin (r-1)) : inverseGenerator r i*T r i=1 := by
  rw [inverseGenerator,sub_mul,T_quadratic,Matrix.smul_mul,one_mul]
  abel

/-- The genuine invertible adjacent braid generator in the actual
permutation-basis Hecke algebra. -/
def generatorUnit (r : ℕ) (i : Fin (r-1)) : (algebra r)ˣ where
  val := ⟨T r i,Algebra.subset_adjoin (Set.mem_range_self i)⟩
  inv := ⟨inverseGenerator r i,(algebra r).sub_mem
    (Algebra.subset_adjoin (Set.mem_range_self i))
    ((algebra r).smul_mem (algebra r).one_mem Polynomial.X)⟩
  val_inv := Subtype.ext (T_mul_inverseGenerator r i)
  inv_val := Subtype.ext (inverseGenerator_mul_T r i)

def wordUnit (r : ℕ) (w : List (Fin (r-1))) : (algebra r)ˣ := (w.map (generatorUnit r)).prod

lemma wordUnit_matrix (r : ℕ) (w : List (Fin (r-1))) :
    (((wordUnit r w : (algebra r)ˣ) : algebra r) : Mat r)=
      wordMatrix adjacentMove descent (Polynomial.X:ℤ[X]) w := by
  induction w with
  | nil => rfl
  | cons i w ih =>
    change T r i*(((wordUnit r w : (algebra r)ˣ) : algebra r) : Mat r)=_
    rw [ih]
    rfl

/-- The actual half twist is a unit, with the concrete inverse obtained
by reversing the word and replacing each T_i by T_i-z. -/
def halfTwistUnit (r : ℕ) : (algebra r)ˣ := wordUnit r (deltaWord (r-1))

lemma halfTwistUnit_matrix (r : ℕ) :
    (((halfTwistUnit r : (algebra r)ˣ) : algebra r) : Mat r)=halfTwist r :=
  wordUnit_matrix r _

def fullTwistUnit (r : ℕ) : (algebra r)ˣ := halfTwistUnit r^2

lemma fullTwistUnit_val (r : ℕ) : (fullTwistUnit r : algebra r)=omega r := by
  apply Subtype.ext
  change ((((halfTwistUnit r : (algebra r)ˣ) : algebra r) : Mat r)^2)=fullTwist r
  rw [halfTwistUnit_matrix]
  rfl

/-- Invertibility of the genuine central full twist, without changing
its existing concrete definition or using a field localization. -/
theorem omega_isUnit (r : ℕ) : IsUnit (omega r) :=
  ⟨fullTwistUnit r,fullTwistUnit_val r⟩

end
end Paper20.HeckeTraceAlgebra
