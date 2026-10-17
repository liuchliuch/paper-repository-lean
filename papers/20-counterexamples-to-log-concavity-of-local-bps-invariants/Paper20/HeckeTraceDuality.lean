import Paper20.CanonicalHecke

namespace Paper20.HeckeTraceAlgebra
open Polynomial Matrix Paper20.HeckeMatrices Paper20.HeckeWalkExpansion
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- Transpose is the actual anti-involution of the generated Hecke
algebra; closure is derived from the symmetric generators. -/
theorem transpose_mem (r : ℕ) (A : Mat r) (hA : A ∈ algebra r) : A.transpose ∈ algebra r := by
  induction hA using Algebra.adjoin_induction with
  | mem A hA =>
    obtain ⟨i,rfl⟩ := hA
    rw [T_transpose]
    exact Algebra.subset_adjoin (Set.mem_range_self i)
  | algebraMap a =>
    have he : ((algebraMap ℤ[X] (Mat r)) a).transpose=(algebraMap ℤ[X] (Mat r)) a := by
      simp [Algebra.algebraMap_eq_smul_one]
    rw [he]
    exact (algebra r).algebraMap_mem a
  | add A B hA hB ihA ihB =>
    rw [Matrix.transpose_add]
    exact (algebra r).add_mem ihA ihB
  | mul A B hA hB ihA ihB =>
    rw [Matrix.transpose_mul]
    exact (algebra r).mul_mem ihB ihA

/-- The transpose of the actual permutation basis extracts its exact
identity-column coordinate under the canonical trace. -/
theorem trace_basisTranspose_mul (r : ℕ) (p : State r) (A : Mat r) :
    trace r ((basisMatrix r p).transpose*A)=A p 1 := by
  classical
  have hc : ∀ s, basisMatrix r p s 1=delta p s := by
    intro s
    have h := congrFun (basisMatrix_delta r p) s
    simpa only [mulVec_delta] using h
  unfold trace
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply,hc,delta,ite_mul,one_mul,zero_mul]
  simp

/-- The actual standard basis and its transposes are dual for this trace. -/
theorem trace_basis_duality (r : ℕ) (p q : State r) :
    trace r ((basisMatrix r p).transpose*basisMatrix r q)=if p=q then 1 else 0 := by
  classical
  rw [trace_basisTranspose_mul]
  have he := congrFun (basisMatrix_delta r q) p
  by_cases hp : p=q <;> simpa only [mulVec_delta,delta,hp,↓reduceIte] using he

/-- Nondegeneracy is proved from actual dual basis coordinates and actual
faithfulness, completing the symmetrizing-trace property. -/
theorem trace_nondegenerate (r : ℕ) (A : Mat r) (hA : A ∈ algebra r)
    (h : ∀ B : Mat r, B ∈ algebra r → trace r (A*B)=0) : A=0 := by
  have hcol : A.mulVec (delta (1 : State r))=0 := by
    funext p
    have hB := transpose_mem r (basisMatrix r p) (basisMatrix_mem r p)
    have he := h (basisMatrix r p).transpose hB
    rw [trace_mul_comm r A _ hA hB,trace_basisTranspose_mul] at he
    simpa only [mulVec_delta,Pi.zero_apply] using he
  apply eq_of_identity_column r A 0 hA (algebra r).zero_mem
  rw [hcol,Matrix.zero_mulVec]

end
end Paper20.HeckeTraceAlgebra
