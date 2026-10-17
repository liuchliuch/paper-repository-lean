import Paper25.Regularization
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.LinearAlgebra.Matrix.Reindex
import Mathlib.Analysis.CStarAlgebra.Matrix

/-!
# Nuclear norm and contraction trace pairing

The trace/nuclear-norm duality needed by equations (10) and (19) is proved
from the positive-semidefinite contraction certificate `I - Q†Q ≥ 0`.
The argument uses an actual orthonormal eigenbasis of `M†M`, with no
singular-value decomposition or trace estimate assumed as a premise.
-/

noncomputable section

open scoped ComplexOrder ComplexConjugate InnerProductSpace
open Matrix

namespace Paper25

section FiniteIndex

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Nuclear norm for arbitrary finite index types, agreeing with `nuclearNorm`
on `Fin m`. -/
def matrixNuclearNorm (M : Matrix ι ι ℂ) : ℝ :=
  ∑ i, Real.sqrt ((Matrix.isHermitian_transpose_mul_self M).eigenvalues i)

lemma euclidean_norm_sq_dot (x : ι → ℂ) :
    ‖WithLp.toLp 2 x‖ ^ 2 = (dotProduct (star x) x).re := by
  rw [@norm_sq_eq_re_inner ℂ]
  change (dotProduct x (star x)).re = _
  rw [dotProduct_comm]

lemma euclidean_mulVec_norm_sq (M : Matrix ι ι ℂ) (x : ι → ℂ) :
    ‖WithLp.toLp 2 (M *ᵥ x)‖ ^ 2 =
      (dotProduct (star x) ((M.conjTranspose * M) *ᵥ x)).re := by
  rw [euclidean_norm_sq_dot]
  congr 1
  symm
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
    Matrix.vecMul_conjTranspose, star_star]

/-- A positive-semidefinite `I-Q†Q` certificate gives the Euclidean
contraction inequality on every vector. -/
theorem contraction_mulVec_norm (Q : Matrix ι ι ℂ)
    (hQ : (1 - Q.conjTranspose * Q).PosSemidef) (x : ι → ℂ) :
    ‖WithLp.toLp 2 (Q *ᵥ x)‖ ≤ ‖WithLp.toLp 2 x‖ := by
  have h := hQ.re_dotProduct_nonneg x
  have he : (dotProduct (star x) ((1 - Q.conjTranspose * Q) *ᵥ x)).re =
      ‖WithLp.toLp 2 x‖ ^ 2 - ‖WithLp.toLp 2 (Q *ᵥ x)‖ ^ 2 := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, Complex.sub_re,
      euclidean_norm_sq_dot, euclidean_mulVec_norm_sq]
  change 0 ≤ (dotProduct (star x) ((1 - Q.conjTranspose * Q) *ᵥ x)).re at h
  rw [he] at h
  nlinarith [norm_nonneg (WithLp.toLp 2 x),
    norm_nonneg (WithLp.toLp 2 (Q *ᵥ x))]

/-- Trace in the orthonormal eigenbasis of the Gram matrix. -/
lemma trace_eq_sum_gram_basis (M N : Matrix ι ι ℂ) :
    N.trace = ∑ i, ⟪(Matrix.isHermitian_transpose_mul_self M).eigenvectorBasis i,
      Matrix.toEuclideanLin N ((Matrix.isHermitian_transpose_mul_self M).eigenvectorBasis i)⟫_ℂ := by
  let hM := Matrix.isHermitian_transpose_mul_self M
  let U : Matrix ι ι ℂ := hM.eigenvectorUnitary
  have hU : U * U.conjTranspose = 1 := hM.eigenvectorUnitary.2.2
  calc
    N.trace = (U.conjTranspose * N * U).trace := by
      rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
    _ = ∑ i, ⟪hM.eigenvectorBasis i,
        Matrix.toEuclideanLin N (hM.eigenvectorBasis i)⟫_ℂ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Matrix.mul_assoc]
      change dotProduct (star (fun j => U j i)) (N *ᵥ (fun j => U j i)) =
        dotProduct (N *ᵥ ⇑(hM.eigenvectorBasis i)) (star ⇑(hM.eigenvectorBasis i))
      rw [dotProduct_comm]
      rfl

/-- The norm of `M` applied to a unit Gram eigenvector is its singular value. -/
lemma norm_mulVec_gram_basis (M : Matrix ι ι ℂ) (i : ι) :
    ‖Matrix.toEuclideanLin M ((Matrix.isHermitian_transpose_mul_self M).eigenvectorBasis i)‖ =
      Real.sqrt ((Matrix.isHermitian_transpose_mul_self M).eigenvalues i) := by
  let hM := Matrix.isHermitian_transpose_mul_self M
  have hs : ‖Matrix.toEuclideanLin M (hM.eigenvectorBasis i)‖ ^ 2 =
      hM.eigenvalues i := by
    rw [Matrix.toEuclideanLin_apply, euclidean_mulVec_norm_sq]
    exact (hM.eigenvalues_eq i).symm
  rw [← hs, Real.sqrt_sq (norm_nonneg _)]

/-- Trace/nuclear-norm duality for a genuine contraction `Q`. -/
theorem trace_mul_le_matrixNuclearNorm (Q M : Matrix ι ι ℂ)
    (hQ : (1 - Q.conjTranspose * Q).PosSemidef) :
    ‖(Q * M).trace‖ ≤ matrixNuclearNorm M := by
  let hM := Matrix.isHermitian_transpose_mul_self M
  rw [trace_eq_sum_gram_basis M (Q * M)]
  unfold matrixNuclearNorm
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro i _
  have hinner := norm_inner_le_norm (𝕜 := ℂ) (hM.eigenvectorBasis i)
    (Matrix.toEuclideanLin (Q * M) (hM.eigenvectorBasis i))
  have hu : ‖hM.eigenvectorBasis i‖ = 1 := hM.eigenvectorBasis.norm_eq_one i
  have hc : ‖Matrix.toEuclideanLin (Q * M) (hM.eigenvectorBasis i)‖ ≤
      ‖Matrix.toEuclideanLin M (hM.eigenvectorBasis i)‖ := by
    simpa only [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using
      contraction_mulVec_norm Q hQ (M *ᵥ ⇑(hM.eigenvectorBasis i))
  calc
    _ ≤ ‖hM.eigenvectorBasis i‖ *
        ‖Matrix.toEuclideanLin (Q * M) (hM.eigenvectorBasis i)‖ := hinner
    _ ≤ ‖Matrix.toEuclideanLin M (hM.eigenvectorBasis i)‖ := by
      simpa only [hu, one_mul] using hc
    _ = _ := norm_mulVec_gram_basis M i

section OperatorNorm

open scoped Matrix.Norms.L2Operator

/-- Full trace/nuclear-norm duality for the actual Euclidean operator norm. -/
theorem trace_mul_le_opNorm_matrixNuclearNorm (Q M : Matrix ι ι ℂ) :
    ‖(Q * M).trace‖ ≤ ‖Q‖ * matrixNuclearNorm M := by
  let hM := Matrix.isHermitian_transpose_mul_self M
  rw [trace_eq_sum_gram_basis M (Q * M)]
  calc
    _ ≤ ∑ i, ‖⟪hM.eigenvectorBasis i,
        Matrix.toEuclideanLin (Q * M) (hM.eigenvectorBasis i)⟫_ℂ‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖Q‖ * Real.sqrt (hM.eigenvalues i) := by
      apply Finset.sum_le_sum
      intro i _
      have hinner := norm_inner_le_norm (𝕜 := ℂ) (hM.eigenvectorBasis i)
        (Matrix.toEuclideanLin (Q * M) (hM.eigenvectorBasis i))
      rw [hM.eigenvectorBasis.norm_eq_one i, one_mul] at hinner
      have hc : ‖Matrix.toEuclideanLin (Q * M) (hM.eigenvectorBasis i)‖ ≤
          ‖Q‖ * ‖Matrix.toEuclideanLin M (hM.eigenvectorBasis i)‖ := by
        have hv := Matrix.l2_opNorm_mulVec Q (Matrix.toEuclideanLin M (hM.eigenvectorBasis i))
        change ‖WithLp.toLp 2 (Q *ᵥ (M *ᵥ ⇑(hM.eigenvectorBasis i)))‖ ≤
          ‖Q‖ * ‖WithLp.toLp 2 (M *ᵥ ⇑(hM.eigenvectorBasis i))‖ at hv
        simpa only [Matrix.toEuclideanLin_apply, Matrix.mulVec_mulVec] using hv
      exact hinner.trans (hc.trans_eq (congrArg (fun r => ‖Q‖ * r)
        (norm_mulVec_gram_basis M i)))
    _ = _ := (Finset.mul_sum _ _ _).symm

/-- Nuclear norm is bounded by dimension times Euclidean operator norm. -/
theorem matrixNuclearNorm_le_card_opNorm (M : Matrix ι ι ℂ) :
    matrixNuclearNorm M ≤ (Fintype.card ι : ℝ) * ‖M‖ := by
  let hM := Matrix.isHermitian_transpose_mul_self M
  calc
    matrixNuclearNorm M = ∑ i, ‖Matrix.toEuclideanLin M (hM.eigenvectorBasis i)‖ := by
      unfold matrixNuclearNorm
      exact Finset.sum_congr rfl (fun i _ => (norm_mulVec_gram_basis M i).symm)
    _ ≤ ∑ _i : ι, ‖M‖ := by
      apply Finset.sum_le_sum
      intro i _
      have h := Matrix.l2_opNorm_mulVec M (hM.eigenvectorBasis i)
      simpa only [hM.eigenvectorBasis.norm_eq_one i, mul_one] using h
    _ = _ := by simp

/-- The magnitude of a trace is at most dimension times operator norm. -/
theorem norm_trace_le_card_opNorm (M : Matrix ι ι ℂ) :
    ‖M.trace‖ ≤ (Fintype.card ι : ℝ) * ‖M‖ := by
  have hI : (1 - (1 : Matrix ι ι ℂ).conjTranspose * 1).PosSemidef := by
    simp only [Matrix.conjTranspose_one, Matrix.one_mul, sub_self]
    exact Matrix.PosSemidef.zero
  have h := trace_mul_le_matrixNuclearNorm 1 M hI
  rw [Matrix.one_mul] at h
  exact h.trans (matrixNuclearNorm_le_card_opNorm M)

/-- The normalized real trace of an error block is bounded by its operator
norm, as used after equation (19). -/
theorem abs_normalized_re_trace_le_opNorm (M : Matrix ι ι ℂ)
    (hcard : 0 < Fintype.card ι) :
    |M.trace.re / (Fintype.card ι : ℝ)| ≤ ‖M‖ := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hcard
  rw [abs_div, abs_of_pos hc, div_le_iff₀ hc]
  exact (Complex.abs_re_le_norm M.trace).trans
    ((norm_trace_le_card_opNorm M).trans_eq (mul_comm _ _))

end OperatorNorm

end FiniteIndex

lemma matrixNuclearNorm_eq {m : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) :
    matrixNuclearNorm M = nuclearNorm M := rfl

/-- The contraction form of trace/nuclear-norm duality in the paper's norm
notation. -/
theorem trace_mul_le_nuclearNorm {m : ℕ} (Q M : Matrix (Fin m) (Fin m) ℂ)
    (hQ : (1 - Q.conjTranspose * Q).PosSemidef) :
    ‖(Q * M).trace‖ ≤ nuclearNorm M :=
  trace_mul_le_matrixNuclearNorm Q M hQ

open scoped Matrix.Norms.L2Operator in
/-- Full duality in the paper's `nuclearNorm` notation. -/
theorem trace_mul_le_opNorm_nuclearNorm {m : ℕ} (Q M : Matrix (Fin m) (Fin m) ℂ) :
    ‖(Q * M).trace‖ ≤ ‖Q‖ * nuclearNorm M :=
  trace_mul_le_opNorm_matrixNuclearNorm Q M

/-- The regularized inverse trace error follows from the actual matrix
Lemma 4 and the selector's contraction certificate. -/
theorem trace_regularization_error {m : ℕ}
    (Q A : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A)
    (hQ : (1 - Q.conjTranspose * Q).PosSemidef) (lam : ℝ) (hlam : 0 < lam) :
    ‖(Q * A⁻¹).trace - (Q * regInv A lam).trace‖ ≤
      (lam / 2) * frobNormSq A⁻¹ := by
  rw [← Matrix.trace_sub, ← Matrix.mul_sub]
  exact (trace_mul_le_nuclearNorm Q _ hQ).trans (lemma_4 A hA lam hlam)

section ArbitraryFiniteIndex

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Squared Frobenius norm on arbitrary finite indices. -/
def matrixFrobNormSq (M : Matrix ι ι ℂ) : ℝ :=
  ∑ i, ∑ j, Complex.normSq (M i j)

/-- The paper's regularized inverse on arbitrary finite indices. -/
def matrixRegInv (A : Matrix ι ι ℂ) (lam : ℝ) : Matrix ι ι ℂ :=
  A.conjTranspose * (A * A.conjTranspose + lam ^ 2 • 1)⁻¹

lemma trace_reindex_eq (e : ι ≃ κ) (M : Matrix ι ι ℂ) :
    (Matrix.reindex e e M).trace = M.trace := by
  change (∑ i, M (e.symm i) (e.symm i)) = ∑ i, M i i
  exact (e.symm.sum_comp (fun i => M i i))

lemma matrixFrobNormSq_reindex (e : ι ≃ κ) (M : Matrix ι ι ℂ) :
    matrixFrobNormSq (Matrix.reindex e e M) = matrixFrobNormSq M := by
  change (∑ i, ∑ j, Complex.normSq (M (e.symm i) (e.symm j))) =
    ∑ i, ∑ j, Complex.normSq (M i j)
  calc
    _ = ∑ i, ∑ j, Complex.normSq (M i (e.symm j)) :=
      (e.symm.sum_comp (fun i => ∑ j, Complex.normSq (M i (e.symm j))))
    _ = _ := Finset.sum_congr rfl (fun i _ =>
      (e.symm.sum_comp (fun j => Complex.normSq (M i j))))

lemma reindex_matrixRegInv (e : ι ≃ κ) (A : Matrix ι ι ℂ) (lam : ℝ) :
    Matrix.reindex e e (matrixRegInv A lam) = matrixRegInv (Matrix.reindex e e A) lam := by
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  have hmul (X Y : Matrix ι ι ℂ) :
      Matrix.reindex e e (X * Y) = Matrix.reindex e e X * Matrix.reindex e e Y :=
    E.map_mul X Y
  have hadd (X Y : Matrix ι ι ℂ) :
      Matrix.reindex e e (X + Y) = Matrix.reindex e e X + Matrix.reindex e e Y :=
    E.map_add X Y
  have hsmul (c : ℝ) (X : Matrix ι ι ℂ) :
      Matrix.reindex e e (c • X) = c • Matrix.reindex e e X := rfl
  have hone : Matrix.reindex e e (1 : Matrix ι ι ℂ) = 1 := E.map_one
  simp only [matrixRegInv, hmul, ← Matrix.inv_reindex e e, hadd, hsmul, hone,
    Matrix.conjTranspose_reindex]

/-- Equation (10)'s unnormalized trace-error bound on arbitrary finite
clock/Liouville product indices, transported along an actual matrix algebra
isomorphism to the matrix Lemma 4. -/
theorem matrix_trace_regularization_error
    (Q A : Matrix ι ι ℂ) (hA : IsUnit A)
    (hQ : (1 - Q.conjTranspose * Q).PosSemidef) (lam : ℝ) (hlam : 0 < lam) :
    ‖(Q * A⁻¹).trace - (Q * matrixRegInv A lam).trace‖ ≤
      (lam / 2) * matrixFrobNormSq A⁻¹ := by
  let e := Fintype.equivFin ι
  let E := Matrix.reindexAlgEquiv ℂ ℂ e
  have hAf : IsUnit (Matrix.reindex e e A) := hA.map E.toMonoidHom
  have hQf : (1 - (Matrix.reindex e e Q).conjTranspose * Matrix.reindex e e Q).PosSemidef := by
    simpa only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv,
      Matrix.submatrix_mul_equiv]
      using hQ.submatrix e.symm
  have h := trace_regularization_error (Matrix.reindex e e Q) (Matrix.reindex e e A)
    hAf hQf lam hlam
  have hmul (X Y : Matrix ι ι ℂ) :
      Matrix.reindex e e (X * Y) = Matrix.reindex e e X * Matrix.reindex e e Y :=
    E.map_mul X Y
  have hreg : regInv (Matrix.reindex e e A) lam =
      Matrix.reindex e e (matrixRegInv A lam) := (reindex_matrixRegInv e A lam).symm
  rw [hreg, Matrix.inv_reindex, ← hmul, ← hmul, trace_reindex_eq, trace_reindex_eq] at h
  change _ ≤ (lam / 2) * matrixFrobNormSq (Matrix.reindex e e A⁻¹) at h
  simpa only [matrixFrobNormSq_reindex] using h

end ArbitraryFiniteIndex

end Paper25
