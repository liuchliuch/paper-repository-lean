import Paper25.CoherentPhaseEstimation
import Paper25.WalkFilter
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-!
# Full-space coherent filtering, relative to the published unitary spectral theorem

The sole external mathematical input is `UnitaryEigenbasis V`: an orthonormal
unitary eigenbasis with unit-modulus eigenvalues, precisely the finite-dimensional
unitary spectral theorem (Axler, *Linear Algebra Done Right*, fourth edition,
Theorem 7.55, printed p. 262; https://linear.axler.net/LADR4e.pdf).
No approximation assertion or filter correctness is included in that input.
The phase parameterization, controlled-power phase estimation, coherent
uncomputation, and transfer of the scalar error to operator norm are proved here.
-/

noncomputable section
open scoped ComplexConjugate ComplexOrder
namespace Paper25

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Explicit external input: the published unitary spectral theorem. -/
structure UnitaryEigenbasis (V : Matrix n n ℂ) where
  basis : Matrix n n ℂ
  basis_unitary : basis ∈ Matrix.unitaryGroup n ℂ
  eigenvalue : n → ℂ
  eigenvalue_norm : ∀ i, ‖eigenvalue i‖ = 1
  decomposition : V = basis * Matrix.diagonal eigenvalue * star basis

namespace UnitaryEigenbasis

variable {V : Matrix n n ℂ} (D : UnitaryEigenbasis V)

/-- Eigenphase in turns, derived from the external eigenvalue rather than assumed. -/
def phase (i : n) : ℝ := Complex.arg (D.eigenvalue i) / (2 * Real.pi)

lemma exp_phase (i : n) :
    Complex.exp (2 * Real.pi * Complex.I * (D.phase i : ℂ)) = D.eigenvalue i := by
  have heq : 2 * Real.pi * Complex.I * (D.phase i : ℂ) =
      (Complex.arg (D.eigenvalue i) : ℂ) * Complex.I := by
    unfold phase
    push_cast
    field_simp
    <;> ring
  rw [heq]
  simpa only [D.eigenvalue_norm i, Complex.ofReal_one, one_mul]
    using Complex.norm_mul_exp_arg_mul_I (D.eigenvalue i)

lemma phase_decomposition :
    V = D.basis * Matrix.diagonal (fun i =>
      Complex.exp (2 * Real.pi * Complex.I * (D.phase i : ℂ))) * star D.basis := by
  simp only [D.exp_phase]
  exact D.decomposition

end UnitaryEigenbasis

lemma unitary_conjugate_pow (W A : Matrix n n ℂ)
    (hW : W ∈ Matrix.unitaryGroup n ℂ) (r : ℕ) :
    (W * A * star W) ^ r = W * A ^ r * star W := by
  induction r with
  | zero => simpa only [pow_zero, mul_one] using hW.2.symm
  | succ r ih => rw [pow_succ, ih, unitary_conjugate_mul W hW, pow_succ]

lemma unitary_conjugate_sum_smul {s : Type*} [Fintype s]
    (W : Matrix n n ℂ) (c : s → ℂ) (A : s → Matrix n n ℂ) :
    (∑ r, c r • (W * A r * star W)) = W * (∑ r, c r • A r) * star W := by
  simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]

/-- The spectral formula for the actual controlled-power phase-estimation zero block. -/
theorem phaseEstimationMatrix_spectral_block (V : Matrix n n ℂ)
    (D : UnitaryEigenbasis V) (M : ℕ) (hM : 0 < M) (j : Fin M) :
    (phaseEstimationMatrix V M).submatrix (fun i => (j, i)) (fun i => (⟨0, hM⟩, i)) =
      D.basis * Matrix.diagonal (fun i => phaseEstAmplitude M (D.phase i) j) * star D.basis := by
  let c : Fin M → ℂ := fun r => inverseFourierMatrix M j r *
    conj (inverseFourierMatrix M ⟨0, hM⟩ r)
  have hp (r : Fin M) : V ^ r.val = D.basis * Matrix.diagonal
      (fun i => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (D.phase i : ℂ))) * star D.basis := by
    conv_lhs => rw [D.phase_decomposition]
    rw [unitary_conjugate_pow _ _ D.basis_unitary, Matrix.diagonal_pow]
    congr 2
    congr 1
    funext i
    simp only [Pi.pow_apply]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hc (i : n) : (∑ r : Fin M, c r *
      Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (D.phase i : ℂ))) =
      phaseEstAmplitude M (D.phase i) j := by
    have h := coherentPhasePreparation_zero_column M (D.phase i) hM j
    unfold coherentPhasePreparation eigenphaseDiagonal at h
    rw [Matrix.mul_apply] at h
    simpa only [Matrix.mul_diagonal, Matrix.star_apply, Complex.star_def, c, mul_assoc,
      mul_comm, mul_left_comm] using h
  rw [phaseEstimationMatrix_block]
  change (∑ r : Fin M, c r • V ^ r.val) = _
  simp only [hp]
  rw [unitary_conjugate_sum_smul]
  congr 2
  ext i k
  by_cases hik : i = k
  · subst k
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply_eq] using hc i
  · simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.diagonal_apply_ne _ hik, mul_zero, Finset.sum_const_zero]

/-- The phase-estimation branch operator for a fixed measured label; no measurement
is performed by the circuit. -/
def phaseBranch (V : Matrix n n ℂ) (M : ℕ) (hM : 0 < M) (j : Fin M) : Matrix n n ℂ :=
  (phaseEstimationMatrix V M).submatrix (fun i => (j, i)) (fun i => (⟨0, hM⟩, i))

lemma unitary_conjugate_gram (W : Matrix n n ℂ) (hW : W ∈ Matrix.unitaryGroup n ℂ)
    (a : n → ℂ) :
    (W * Matrix.diagonal a * star W).conjTranspose * (W * Matrix.diagonal a * star W) =
      W * Matrix.diagonal (fun i => ((‖a i‖ ^ 2 : ℝ) : ℂ)) * star W := by
  change star (W * Matrix.diagonal a * star W) * (W * Matrix.diagonal a * star W) = _
  have hs : star (W * Matrix.diagonal a * star W) = W * star (Matrix.diagonal a) * star W := by
    simp only [star_mul, star_star, mul_assoc]
  rw [hs, unitary_conjugate_mul W hW]
  congr 2
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  congr 1
  funext i
  change conj (a i) * a i = _
  simpa only [Complex.ofReal_pow] using Complex.conj_mul' (a i)

lemma phaseBranch_gram (V : Matrix n n ℂ) (D : UnitaryEigenbasis V)
    (M : ℕ) (hM : 0 < M) (j : Fin M) :
    (phaseBranch V M hM j).conjTranspose * phaseBranch V M hM j =
      D.basis * Matrix.diagonal (fun i => ((phaseEstProb M (D.phase i) j : ℝ) : ℂ)) * star D.basis := by
  rw [phaseBranch, phaseEstimationMatrix_spectral_block V D M hM j]
  exact unitary_conjugate_gram D.basis D.basis_unitary _

/-- The compressed coherent rotation/uncomputation block. -/
def phaseFilteredBlock (V : Matrix n n ℂ) (M : ℕ) (hM : 0 < M) (g : Fin M → ℝ) : Matrix n n ℂ :=
  ∑ j, (g j : ℂ) • ((phaseBranch V M hM j).conjTranspose * phaseBranch V M hM j)

lemma phaseFilteredBlock_spectral (V : Matrix n n ℂ) (D : UnitaryEigenbasis V)
    (M : ℕ) (hM : 0 < M) (g : Fin M → ℝ) :
    phaseFilteredBlock V M hM g = D.basis * Matrix.diagonal (fun i =>
      ((∑ j, phaseEstProb M (D.phase i) j * g j : ℝ) : ℂ)) * star D.basis := by
  unfold phaseFilteredBlock
  simp only [phaseBranch_gram V D M hM]
  rw [unitary_conjugate_sum_smul]
  congr 2
  ext i k
  by_cases hik : i = k
  · subst k
    simp [Matrix.sum_apply, Matrix.smul_apply, mul_comm]
  · simp [Matrix.sum_apply, Matrix.smul_apply, Matrix.diagonal_apply_ne _ hik]

end Paper25
