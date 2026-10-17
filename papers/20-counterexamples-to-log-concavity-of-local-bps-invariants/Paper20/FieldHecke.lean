import Paper20.CanonicalHecke
import Paper20.PresentedDimension

namespace Paper20.FieldHecke
open Polynomial Matrix Module Paper20.HeckeTraceAlgebra Paper20.HeckeMatrices
open Paper20.HeckeWalkExpansion
noncomputable section
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

section Field
variable {F : Type*} [Field F]

abbrev FieldMat (r : ℕ) := Matrix (State r) (State r) F

def scalarEval (z : F) : ℤ[X] →+* F := Polynomial.eval₂RingHom (Int.castRingHom F) z

def matrixEval (r : ℕ) (z : F) : Mat r →+* FieldMat (F:=F) r := (scalarEval z).mapMatrix

def fieldT (r : ℕ) (z : F) (i : Fin (r-1)) : FieldMat (F:=F) r := matrixEval r z (T r i)

/-- The original actual permutation-matrix Hecke model after genuine
coefficient specialization to an arbitrary field parameter. -/
def fieldAlgebra (r : ℕ) (z : F) : Subalgebra F (FieldMat (F:=F) r) :=
  Algebra.adjoin F (Set.range (fieldT r z))

lemma matrixEval_smul (r : ℕ) (z : F) (c : ℤ[X]) (A : Mat r) :
    matrixEval r z (c • A)=scalarEval z c • matrixEval r z A := by
  apply Matrix.ext
  intro s t
  change scalarEval z (c*A s t)=scalarEval z c*scalarEval z (A s t)
  exact map_mul _ _ _

theorem fieldT_quadratic (r : ℕ) (z : F) (i : Fin (r-1)) :
    fieldT r z i^2=z • fieldT r z i+1 := by
  have he := congrArg (matrixEval r z) (T_quadratic r i)
  rw [map_mul,map_add,map_one,matrixEval_smul] at he
  have hX : scalarEval z Polynomial.X=z := Polynomial.eval₂_X (Int.castRingHom F) z
  rw [hX] at he
  simpa only [fieldT,pow_two,add_comm] using he

theorem fieldT_braid (r : ℕ) (z : F) (i j : Fin (r-1)) (h : j.val=i.val+1) :
    fieldT r z i*fieldT r z j*fieldT r z i=fieldT r z j*fieldT r z i*fieldT r z j := by
  simpa only [fieldT,map_mul] using congrArg (matrixEval r z) (T_braid r i j h)

theorem fieldT_commute (r : ℕ) (z : F) (i j : Fin (r-1))
    (h : i.val+1 < j.val ∨ j.val+1 < i.val) : fieldT r z i*fieldT r z j=fieldT r z j*fieldT r z i := by
  simpa only [fieldT,map_mul] using congrArg (matrixEval r z) (T_commute r i j h)

/-- Every specialized element of the original actual polynomial Hecke
algebra lies in the actual field-generated model. -/
theorem matrixEval_mem (r : ℕ) (z : F) (A : Mat r) (hA : A ∈ algebra r) :
    matrixEval r z A ∈ fieldAlgebra r z := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    obtain ⟨i,rfl⟩ := hA
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  | algebraMap c =>
    rw [Algebra.algebraMap_eq_smul_one,matrixEval_smul,map_one]
    exact (fieldAlgebra r z).smul_mem (fieldAlgebra r z).one_mem (scalarEval z c)
  | add A B hA hB ia ib => rw [map_add]; exact (fieldAlgebra r z).add_mem ia ib
  | mul A B hA hB ia ib => rw [map_mul]; exact (fieldAlgebra r z).mul_mem ia ib

def fieldBasis (r : ℕ) (z : F) (p : State r) : FieldMat (F:=F) r :=
  matrixEval r z (basisMatrix r p)

theorem fieldBasis_mem (r : ℕ) (z : F) (p : State r) : fieldBasis r z p ∈ fieldAlgebra r z :=
  matrixEval_mem r z _ (basisMatrix_mem r p)

/-- Each original actual basis element retains its exact identity column
at every field parameter, so independence cannot be lost on specialization. -/
theorem fieldBasis_column (r : ℕ) (z : F) (p s : State r) :
    fieldBasis r z p s 1=if s=p then 1 else 0 := by
  have he := congrFun (basisMatrix_delta r p) s
  simp only [mulVec_delta,delta] at he
  change scalarEval z (basisMatrix r p s 1)=_
  rw [he]
  split_ifs <;> simp

theorem fieldBasis_independent (r : ℕ) (z : F) : LinearIndependent F (fieldBasis r z) := by
  let col : FieldMat (F:=F) r →ₗ[F] (State r → F) :=
    { toFun := fun A s => A s 1
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  have hc (p : State r) : col (fieldBasis r z p)=Pi.basisFun F (State r) p := by
    funext s
    simp only [col,LinearMap.coe_mk,AddHom.coe_mk,fieldBasis_column,Pi.basisFun_apply,
      Pi.single_apply,eq_comm]
  have hi : LinearIndependent F (fun p => col (fieldBasis r z p)) := by
    simp_rw [hc]
    exact (Pi.basisFun F (State r)).linearIndependent
  exact LinearIndependent.of_comp col hi

def basisElement (r : ℕ) (z : F) (p : State r) : fieldAlgebra r z :=
  ⟨fieldBasis r z p,fieldBasis_mem r z p⟩

theorem basisElement_independent (r : ℕ) (z : F) : LinearIndependent F (basisElement r z) :=
  LinearIndependent.of_comp (fieldAlgebra r z).val.toLinearMap (fieldBasis_independent r z)

end Field
end
end Paper20.FieldHecke
