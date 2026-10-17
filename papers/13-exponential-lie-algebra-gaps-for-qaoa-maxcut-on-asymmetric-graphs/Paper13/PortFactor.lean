import Paper13.LocalProjector
import Mathlib.LinearAlgebra.Matrix.Reindex
noncomputable section
namespace Paper13
open Matrix
open scoped Kronecker

/-- Separating the fifth qubit from the six singlet qubits. -/
def portBasis : (Fin 2 × QubitBasis 6) ≃ QubitBasis 7 where
  toFun p := ![p.2 0, p.2 1, p.2 2, p.2 3, p.1, p.2 4, p.2 5]
  invFun x := (x 4, ![x 0, x 1, x 2, x 3, x 5, x 6])
  left_inv p := by
    rcases p with ⟨b,x⟩
    apply Prod.ext
    · rfl
    · funext i; fin_cases i <;> rfl
  right_inv x := by funext i; fin_cases i <;> rfl

lemma portBasis_swap1 (x : Fin 2 × QubitBasis 6) :
    swapBasis 0 2 (portBasis x) = portBasis (x.1, swapBasis 0 2 x.2) := by
  funext w
  fin_cases w <;> simp [portBasis, swapBasis_apply]

lemma portBasis_swap2 (x : Fin 2 × QubitBasis 6) :
    swapBasis 1 6 (portBasis x) = portBasis (x.1, swapBasis 1 5 x.2) := by
  funext w
  fin_cases w <;> simp [portBasis, swapBasis_apply]

lemma portBasis_swap3 (x : Fin 2 × QubitBasis 6) :
    swapBasis 3 5 (portBasis x) = portBasis (x.1, swapBasis 3 4 x.2) := by
  funext w
  fin_cases w <;> simp [portBasis, swapBasis_apply]

lemma reindex_port_swap (a b : Fin 7) (c d : Fin 6)
    (h : ∀ x, swapBasis a b (portBasis x) = portBasis (x.1, swapBasis c d x.2)) :
    Matrix.reindexAlgEquiv ℂ ℂ portBasis.symm (swapAt a b) =
      (1 : Op1) ⊗ₖ swapAt c d := by
  ext x y
  change (if portBasis x = swapBasis a b (portBasis y) then (1 : ℂ) else 0) =
    (1 : Op1) x.1 y.1 * swapAt c d x.2 y.2
  simp only [h, portBasis.injective.eq_iff]
  simp only [Prod.ext_iff, Matrix.one_apply, swapAt]
  split_ifs <;> simp_all

/-- The six-qubit rank-one tensor product of the three singlets. -/
def localP0 : Op 6 := singletProj 0 2 * singletProj 1 5 * singletProj 3 4

/-- The literal tensor factorization claimed in Lemma 3. -/
theorem localP_tensor_factor :
    Matrix.reindexAlgEquiv ℂ ℂ portBasis.symm localP = (1 : Op1) ⊗ₖ localP0 := by
  have hs (a b : Fin 7) (c d : Fin 6)
      (h : ∀ x, swapBasis a b (portBasis x) = portBasis (x.1, swapBasis c d x.2)) :
      Matrix.reindexAlgEquiv ℂ ℂ portBasis.symm (singletProj a b) = (1 : Op1) ⊗ₖ singletProj c d := by
    simp only [singletProj, map_smul, map_sub, map_one, reindex_port_swap a b c d h]
    rw [Matrix.kronecker_smul]
    congr 1
    ext ⟨i,x⟩ ⟨j,y⟩
    simp only [Matrix.kronecker_apply, Matrix.sub_apply, Matrix.one_apply, Prod.mk.injEq]
    split_ifs <;> simp_all
  rw [localP, map_mul, map_mul, hs 0 2 0 2 portBasis_swap1,
    hs 1 6 1 5 portBasis_swap2, hs 3 5 3 4 portBasis_swap3]
  rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul]
  simp only [one_mul, localP0]
end Paper13
