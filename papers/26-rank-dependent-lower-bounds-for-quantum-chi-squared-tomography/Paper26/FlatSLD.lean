import Paper26.AlignedFisherBudget
import Paper26.WeightedTraceCS

/-!
# Explicit SLDs for the actual flat-state graph tangents

The base state is the actual flat graph state at `X=0`, and the tangent is
`AlignedFisherBudget.tangent K`.  The SLD is the explicit Hermitian
`2 (V K U† + U K† V†)`.  Its equation, zero mean, energy, and unitary
transport are native finite matrix identities.  The final real contraction
budget uses the actual `MatrixCoordinates` equivalence and Euclidean basis.
No external Fisher or SLD input is used.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal

namespace Paper26.FlatSLD

open QuantumModel Normalization PositiveLossBridge AlignedFisherBudget

variable {κ σ : Type*} [Fintype κ] [DecidableEq κ] [Fintype σ] [DecidableEq σ]

/-- The actual canonical rank-`card κ` flat state. -/
def baseState [Nonempty κ] : Density (κ ⊕ σ) :=
  GraphFamily.density (0 : Matrix σ κ ℂ)

/-- The complete actual Hermitian off-diagonal matrix. -/
def offDiagonal (K : Matrix σ κ ℂ) : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ :=
  complementColumns * K * sourceColumnsᴴ + sourceColumns * Kᴴ * complementColumnsᴴ

/-- The explicit SLD of the actual graph density tangent. -/
def sld (K : Matrix σ κ ℂ) : Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ := (2 : ℝ) • offDiagonal K

theorem offDiagonal_blocks (K : Matrix σ κ ℂ) :
    offDiagonal K = Matrix.fromBlocks 0 Kᴴ K 0 := by
  simp only [offDiagonal, sourceColumns, complementColumns,
    Matrix.conjTranspose_fromRows_eq_fromCols_conjTranspose,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.fromRows_mul,
    Matrix.one_mul, Matrix.zero_mul]
  ext i j
  cases i <;> cases j <;> simp

theorem sld_blocks (K : Matrix σ κ ℂ) :
    sld K = (2 : ℝ) • Matrix.fromBlocks 0 Kᴴ K 0 := by rw [sld, offDiagonal_blocks]

theorem baseState_matrix [Nonempty κ] :
    (baseState (κ := κ) (σ := σ)).matrix = ((Fintype.card κ : ℝ)⁻¹) •
      Matrix.fromBlocks 1 0 0 0 := by
  rw [baseState, GraphFamily.density_matrix, GraphFamily.projectorMatrix_blocks]
  simp only [GraphFamily.metric, Matrix.conjTranspose_zero, Matrix.mul_zero,
    add_zero, inv_one, Matrix.zero_mul]

/-- The SLD is genuinely Hermitian, independently of the input tangent. -/
theorem sld_hermitian (K : Matrix σ κ ℂ) : (sld K).IsHermitian := by
  rw [sld_blocks]
  change ((2 : ℝ) • Matrix.fromBlocks 0 Kᴴ K 0)ᴴ = _
  rw [Matrix.conjTranspose_smul, star_trivial]
  congr 1
  ext i j
  cases i <;> cases j <;> simp [Matrix.conjTranspose_apply]

/-- The actual matrix SLD equation, in the tensor module's complex-scalar convention. -/
theorem sld_equation [Nonempty κ] (K : Matrix σ κ ℂ) :
    (baseState (κ := κ) (σ := σ)).matrix * sld K +
      sld K * (baseState (κ := κ) (σ := σ)).matrix =
        (2 : ℂ) • tangent K := by
  rw [baseState_matrix, sld_blocks, tangent_blocks]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.mul_one, Matrix.zero_mul, Matrix.mul_zero,
    add_zero]
  ext i j
  cases i <;> cases j <;>
    simp [Matrix.smul_apply, Complex.real_smul, smul_eq_mul] <;> ring

/-- The exact square of the explicit off-diagonal SLD. -/
theorem sld_square (K : Matrix σ κ ℂ) :
    sld K * sld K = (4 : ℝ) • Matrix.fromBlocks (Kᴴ * K) 0 0 (K * Kᴴ) := by
  rw [sld_blocks]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.fromBlocks_multiply,
    Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero]
  norm_num

/-- The SLD has zero expectation in the actual canonical density. -/
theorem sld_mean_zero [Nonempty κ] (K : Matrix σ κ ℂ) :
    (Matrix.trace ((baseState (κ := κ) (σ := σ)).matrix * sld K)).re = 0 := by
  rw [baseState_matrix, sld_blocks]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  simp [Matrix.trace, Fintype.sum_sum_type]

/-- Exact canonical quantum Fisher energy in the actual rectangular Frobenius norm. -/
theorem sld_energy [Nonempty κ] (K : Matrix σ κ ℂ) :
    (Matrix.trace ((baseState (κ := κ) (σ := σ)).matrix * (sld K * sld K))).re =
      4 / (Fintype.card κ : ℝ) * ShellAccounting.frobeniusSq K := by
  rw [baseState_matrix, sld_square]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.fromBlocks_multiply,
    Matrix.one_mul, Matrix.zero_mul, Matrix.mul_zero, add_zero]
  rw [Matrix.trace_smul]
  have ht : Matrix.trace (Matrix.fromBlocks (Kᴴ * K) (0 : Matrix κ σ ℂ)
      (0 : Matrix σ κ ℂ) (0 : Matrix σ σ ℂ)) = Matrix.trace (Kᴴ * K) := by
    simp [Matrix.trace, Fintype.sum_sum_type]
  rw [ht]
  simp only [Complex.smul_re, smul_eq_mul, ← ShellAccounting.frobeniusSq_eq_trace']
  ring

/-- The actual ambient-unitary transport of the base density. -/
def rotateState [Nonempty κ] (W : Matrix.unitaryGroup (κ ⊕ σ) ℂ) : Density (κ ⊕ σ) :=
  conjugateDensity W baseState

/-- The transported actual Hermitian SLD. -/
def rotateSLD (W : Matrix.unitaryGroup (κ ⊕ σ) ℂ) (K : Matrix σ κ ℂ) :
    Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ := conjugate (W : Matrix _ _ ℂ) (sld K)

/-- The transported actual density tangent. -/
def rotateTangent (W : Matrix.unitaryGroup (κ ⊕ σ) ℂ) (K : Matrix σ κ ℂ) :
    Matrix (κ ⊕ σ) (κ ⊕ σ) ℂ := conjugate (W : Matrix _ _ ℂ) (tangent K)

theorem rotateSLD_hermitian (W : Matrix.unitaryGroup (κ ⊕ σ) ℂ) (K : Matrix σ κ ℂ) :
    (rotateSLD W K).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (sld_hermitian K)

theorem rotateSLD_equation [Nonempty κ] (W : Matrix.unitaryGroup (κ ⊕ σ) ℂ)
    (K : Matrix σ κ ℂ) :
    (rotateState W).matrix * rotateSLD W K + rotateSLD W K * (rotateState W).matrix =
      (2 : ℂ) • rotateTangent W K := by
  simp only [rotateState, conjugateDensity_matrix, rotateSLD, rotateTangent]
  rw [← conjugate_mul _ _ _ (unitary_left W), ← conjugate_mul _ _ _ (unitary_left W),
    ← conjugate_add, sld_equation, conjugate_smul]

theorem rotateSLD_mean_zero [Nonempty κ] (W : Matrix.unitaryGroup (κ ⊕ σ) ℂ)
    (K : Matrix σ κ ℂ) :
    (Matrix.trace ((rotateState W).matrix * rotateSLD W K)).re = 0 := by
  change (Matrix.trace (conjugate (W : Matrix _ _ ℂ) baseState.matrix *
    conjugate (W : Matrix _ _ ℂ) (sld K))).re = 0
  rw [← conjugate_mul _ _ _ (unitary_left W), trace_conjugate _ _ (unitary_left W)]
  exact sld_mean_zero K

theorem rotateSLD_energy [Nonempty κ] (W : Matrix.unitaryGroup (κ ⊕ σ) ℂ)
    (K : Matrix σ κ ℂ) :
    (Matrix.trace ((rotateState W).matrix * (rotateSLD W K * rotateSLD W K))).re =
      4 / (Fintype.card κ : ℝ) * ShellAccounting.frobeniusSq K := by
  change (Matrix.trace (conjugate (W : Matrix _ _ ℂ) baseState.matrix *
    (conjugate (W : Matrix _ _ ℂ) (sld K) * conjugate (W : Matrix _ _ ℂ) (sld K)))).re = _
  rw [← conjugate_mul _ _ _ (unitary_left W),
    ← conjugate_mul _ _ _ (unitary_left W), trace_conjugate _ _ (unitary_left W)]
  exact sld_energy K

/-- A real contraction sends every genuine Euclidean orthonormal basis vector
to an actual matrix direction of Frobenius square at most one. -/
theorem contraction_direction_frobenius_le (r s : ℕ)
    (T : EuclideanSpace ℝ (Fin (2 * r * s)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * r * s)))
    (hT : ‖T‖ ≤ 1) (i : Fin (2 * r * s)) :
    ShellAccounting.frobeniusSq ((MatrixCoordinates.coordinates r s).symm
      (T (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i))) ≤ 1 := by
  rw [MatrixCoordinates.frobeniusSq_symm_eq_norm_sq]
  have h := T.le_opNorm (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i)
  rw [OrthonormalBasis.norm_eq_one, mul_one] at h
  have hn := h.trans hT
  nlinarith [norm_nonneg (T (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i))]

/-- Summing the actual SLD energies over all `p=2rs` real orthonormal
coordinate directions after an arbitrary real contraction gives `4p/r=8s`. -/
theorem contraction_energy_sum_le (r s : ℕ) [Nonempty (Fin r)]
    (T : EuclideanSpace ℝ (Fin (2 * r * s)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * r * s)))
    (hT : ‖T‖ ≤ 1) :
    (∑ i : Fin (2 * r * s), (Matrix.trace
      ((baseState (κ := Fin r) (σ := Fin s)).matrix *
        (sld ((MatrixCoordinates.coordinates r s).symm
          (T (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i))) *
        sld ((MatrixCoordinates.coordinates r s).symm
          (T (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i)))))).re) ≤ 8 * s := by
  have hr : (r : ℝ) ≠ 0 := by
    exact_mod_cast (show r ≠ 0 by simpa only [Fintype.card_fin] using
      (Fintype.card_ne_zero (α := Fin r)))
  calc
    _ = ∑ i : Fin (2 * r * s), 4 / (r : ℝ) * ShellAccounting.frobeniusSq
        ((MatrixCoordinates.coordinates r s).symm
          (T (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i))) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [Fintype.card_fin] using sld_energy
        ((MatrixCoordinates.coordinates r s).symm
          (T (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i)))
    _ ≤ ∑ _i : Fin (2 * r * s), (4 / (r : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_one] using mul_le_mul_of_nonneg_left
        (contraction_direction_frobenius_le r s T hT i) (by positivity : 0 ≤ 4 / (r : ℝ))
    _ = 8 * s := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      field_simp
      ring

/-- The actual rectangular direction obtained from a real contracted basis vector. -/
def contractedDirection (r s : ℕ)
    (T : EuclideanSpace ℝ (Fin (2 * r * s)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * r * s)))
    (i : Fin (2 * r * s)) : Matrix (Fin s) (Fin r) ℂ :=
  (MatrixCoordinates.coordinates r s).symm
    (T (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i))

/-- The same complete `8s` budget holds after every actual ambient unitary rotation. -/
theorem rotate_contraction_energy_sum_le (r s : ℕ) [Nonempty (Fin r)]
    (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ)
    (T : EuclideanSpace ℝ (Fin (2 * r * s)) →L[ℝ] EuclideanSpace ℝ (Fin (2 * r * s)))
    (hT : ‖T‖ ≤ 1) :
    (∑ i : Fin (2 * r * s), (Matrix.trace ((rotateState W).matrix *
      (rotateSLD W (contractedDirection r s T i) *
        rotateSLD W (contractedDirection r s T i)))).re) ≤ 8 * s := by
  calc
    _ = ∑ i : Fin (2 * r * s), (Matrix.trace
        ((baseState (κ := Fin r) (σ := Fin s)).matrix *
          (sld (contractedDirection r s T i) * sld (contractedDirection r s T i)))).re := by
      apply Finset.sum_congr rfl
      intro i _
      rw [rotateSLD_energy, sld_energy]
    _ ≤ 8 * s := contraction_energy_sum_le r s T hT

end Paper26.FlatSLD
