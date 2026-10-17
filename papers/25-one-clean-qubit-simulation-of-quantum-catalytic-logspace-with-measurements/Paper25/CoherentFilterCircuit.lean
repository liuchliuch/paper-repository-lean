import Paper25.CoherentPhaseEstimation
import Paper25.WalkFilter

/-!
# The complete rotation and inverse-phase-estimation circuit

The extra rotation qubit is the outer sum index.  Its controlled rotations are
ordinary real rotations, reindexed from SELECT; phase estimation is applied on
both rotation branches.  The all-zero block is proved to equal the weighted
sum of phase-branch Gram matrices.
-/

noncomputable section
open scoped ComplexConjugate
namespace Paper25

variable {s n : Type*} [Fintype s] [DecidableEq s] [Fintype n] [DecidableEq n]

/-- Reordering the rotation, phase, and data registers. -/
def rotationIndex : Sum (s × n) (s × n) ≃ s × (Fin 2 × n) where
  toFun p := match p with
    | Sum.inl (j, i) => (j, (0, i))
    | Sum.inr (j, i) => (j, (1, i))
  invFun p := if p.2.1 = 0 then Sum.inl (p.1, p.2.2) else Sum.inr (p.1, p.2.2)
  left_inv p := by rcases p with ⟨j, i⟩ | ⟨j, i⟩ <;> simp
  right_inv p := by rcases p with ⟨j, b, i⟩; fin_cases b <;> simp

lemma unitary_reindex_matrix {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (A : Matrix b b ℂ)
    (hA : A ∈ Matrix.unitaryGroup b ℂ) : A.submatrix e e ∈ Matrix.unitaryGroup a ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (A.submatrix e e).conjTranspose * A.submatrix e e = 1
  rw [Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv,
    show A.conjTranspose * A = 1 from hA.1, Matrix.submatrix_one_equiv]

/-- Label-controlled one-qubit rotations, with all data qubits left untouched. -/
def labelRotation (g : s → ℝ) : Matrix (Sum (s × n) (s × n)) (Sum (s × n) (s × n)) ℂ :=
  (selectMatrix (fun j => Matrix.kronecker (amplitudeRotation (g j)) (1 : Matrix n n ℂ))).submatrix
    rotationIndex rotationIndex

lemma labelRotation_unitary (g : s → ℝ) (hg : ∀ j, |g j| ≤ 1) :
    labelRotation (n := n) g ∈ Matrix.unitaryGroup (Sum (s × n) (s × n)) ℂ := by
  apply unitary_reindex_matrix
  apply selectMatrix_unitary
  intro j
  exact Matrix.kronecker_mem_unitary (amplitudeRotation_unitary _ (hg j))
    (Matrix.unitaryGroup n ℂ).one_mem

lemma labelRotation_zero_block (g : s → ℝ) :
    (labelRotation (n := n) g).toBlocks₁₁ = selectMatrix (fun j => (g j : ℂ) • (1 : Matrix n n ℂ)) := by
  ext ⟨j, a⟩ ⟨k, b⟩
  change labelRotation (n := n) g (Sum.inl (j, a)) (Sum.inl (k, b)) = _
  simp [labelRotation, Matrix.submatrix_apply, rotationIndex, selectMatrix, Matrix.kronecker, Matrix.kronecker_apply,
    amplitudeRotation, realRotation, Matrix.of_apply, Matrix.one_apply]

/-- Apply the same phase estimation on both values of the rotation qubit. -/
def phaseLift (P : Matrix (s × n) (s × n) ℂ) :
    Matrix (Sum (s × n) (s × n)) (Sum (s × n) (s × n)) ℂ :=
  Matrix.fromBlocks P 0 0 P

lemma phaseLift_unitary (P : Matrix (s × n) (s × n) ℂ)
    (hP : P ∈ Matrix.unitaryGroup (s × n) ℂ) :
    phaseLift P ∈ Matrix.unitaryGroup (Sum (s × n) (s × n)) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  change (phaseLift P).conjTranspose * phaseLift P = 1
  unfold phaseLift
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    show P.conjTranspose * P = 1 from hP.1]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.fromBlocks, Matrix.one_apply]

/-- Prepare phase estimation, rotate coherently, and uncompute phase estimation. -/
def phaseFilterCircuit (P : Matrix (s × n) (s × n) ℂ) (g : s → ℝ) :
    Matrix (Sum (s × n) (s × n)) (Sum (s × n) (s × n)) ℂ :=
  star (phaseLift P) * labelRotation g * phaseLift P

theorem phaseFilterCircuit_unitary (P : Matrix (s × n) (s × n) ℂ) (g : s → ℝ)
    (hP : P ∈ Matrix.unitaryGroup (s × n) ℂ) (hg : ∀ j, |g j| ≤ 1) :
    phaseFilterCircuit P g ∈ Matrix.unitaryGroup (Sum (s × n) (s × n)) ℂ := by
  have hL := phaseLift_unitary P hP
  exact (Matrix.unitaryGroup _ ℂ).mul_mem
    ((Matrix.unitaryGroup _ ℂ).mul_mem (unitary.star_mem hL) (labelRotation_unitary g hg)) hL

lemma phaseFilterCircuit_zero_rotation (P : Matrix (s × n) (s × n) ℂ) (g : s → ℝ) :
    (phaseFilterCircuit P g).toBlocks₁₁ =
      star P * selectMatrix (fun j => (g j : ℂ) • (1 : Matrix n n ℂ)) * P := by
  unfold phaseFilterCircuit phaseLift
  rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose]
  rw [← Matrix.fromBlocks_toBlocks (labelRotation (n := n) g)]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add,
    Matrix.toBlocks_fromBlocks₁₁, Matrix.fromBlocks_toBlocks, labelRotation_zero_block]
  rfl

/-- The exact amplitude block after coherent uncomputation: branch probabilities
are Gram matrices of the actual phase-estimation blocks. -/
theorem phaseFilterCircuit_selected (P : Matrix (s × n) (s × n) ℂ) (g : s → ℝ) (q : s) :
    (phaseFilterCircuit P g).submatrix (fun i => Sum.inl (q, i)) (fun i => Sum.inl (q, i)) =
      ∑ j : s, (g j : ℂ) •
        ((P.submatrix (fun i => (j, i)) (fun i => (q, i))).conjTranspose *
          P.submatrix (fun i => (j, i)) (fun i => (q, i))) := by
  have h := phaseFilterCircuit_zero_rotation P g
  ext a b
  have hab := congr_fun (congr_fun h (q, a)) (q, b)
  change phaseFilterCircuit P g (Sum.inl (q, a)) (Sum.inl (q, b)) = _ at hab
  change phaseFilterCircuit P g (Sum.inl (q, a)) (Sum.inl (q, b)) = _
  rw [hab]
  simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.star_apply, selectMatrix,
    Matrix.one_apply, Matrix.sum_apply, Matrix.smul_apply, Matrix.conjTranspose_apply,
    Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm]

end Paper25
