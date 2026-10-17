import Paper25.BlockEncoding
import Paper25.PhaseEstNormalization

/-!
# A coherent phase-estimation matrix and the filter block

The inverse Fourier matrix is proved unitary from finite-grid orthogonality.
On an eigenspace of phase φ, phase estimation is inverse-Fourier × phase ×
Fourier. Its zero column is exactly the Appendix B amplitude. Combining this
with the real rotations and their uncomputation proves equation (16) for the
actual finite phase-estimation distribution.
-/

noncomputable section
open scoped ComplexConjugate
namespace Paper25

/-- The normalized inverse discrete Fourier transform. -/
def inverseFourierMatrix (M : ℕ) : Matrix (Fin M) (Fin M) ℂ :=
  fun j r => (((Real.sqrt M)⁻¹ : ℝ) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (0 - (j : ℂ) / M))

lemma inverseFourier_column_product (M : ℕ) (a b k : Fin M) :
    conj (inverseFourierMatrix M k a) * inverseFourierMatrix M k b =
      ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) ^ 2) *
        Complex.exp (2 * Real.pi * Complex.I * ((a : ℂ) - b) * ((k : ℂ) / M)) := by
  unfold inverseFourierMatrix
  rw [map_mul, Complex.conj_ofReal]
  have hp := phase_kernel_product M 0 b a k
  push_cast at hp
  simp only [mul_zero, Complex.exp_zero, one_mul] at hp
  calc
    _ = ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) ^ 2) *
        (conj (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * (0 - (k : ℂ) / M))) *
          Complex.exp (2 * Real.pi * Complex.I * (b : ℂ) * (0 - (k : ℂ) / M))) := by ring
    _ = _ := by rw [hp]

lemma fourier_normalization (M : ℕ) (hM : 0 < M) :
    ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) ^ 2) = (M : ℂ)⁻¹ := by
  have h : ((Real.sqrt M)⁻¹ : ℝ) ^ 2 = (M : ℝ)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (by positivity)]
  rw [← Complex.ofReal_pow, h, Complex.ofReal_inv, Complex.ofReal_natCast]

/-- The Fourier transform is an actual unitary matrix. -/
theorem inverseFourierMatrix_unitary (M : ℕ) (hM : 0 < M) :
    inverseFourierMatrix M ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  ext a b
  simp only [Matrix.mul_apply, Matrix.star_apply, Complex.star_def,
    inverseFourier_column_product]
  rw [← Finset.mul_sum, phase_grid_orthogonality M hM a b, fourier_normalization M hM]
  by_cases hab : a = b
  · subst b
    simp [Matrix.one_apply, (show (M : ℂ) ≠ 0 by exact_mod_cast hM.ne')]
  · simp [hab, Matrix.one_apply]

/-- Controlled powers on a φ eigenspace: the r branch acquires e^(2πirφ). -/
def eigenphaseDiagonal (M : ℕ) (φ : ℝ) : Matrix (Fin M) (Fin M) ℂ :=
  Matrix.diagonal (fun r => Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * φ))

lemma exp_imaginary_unitary (x : ℝ) :
    conj (Complex.exp (Complex.I * (x : ℂ))) * Complex.exp (Complex.I * (x : ℂ)) = 1 := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  simp

lemma eigenphaseDiagonal_unitary (M : ℕ) (φ : ℝ) :
    eigenphaseDiagonal M φ ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff']
  unfold eigenphaseDiagonal
  rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal]
  have hu (a : Fin M) : star (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * φ)) *
      Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * φ) = 1 := by
    have heq : 2 * Real.pi * Complex.I * (a : ℂ) * φ =
        Complex.I * ((2 * Real.pi * (a : ℝ) * φ : ℝ) : ℂ) := by push_cast; ring
    change conj (Complex.exp _) * Complex.exp _ = 1
    rw [heq, exp_imaginary_unitary]
  change (Matrix.diagonal (fun a : Fin M => star (Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * φ)) *
    Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) * φ))) = 1
  simpa only [hu] using (Matrix.diagonal_one (n := Fin M) (α := ℂ))

/-- The phase-estimation action on a fixed V eigenspace. -/
def coherentPhasePreparation (M : ℕ) (φ : ℝ) : Matrix (Fin M) (Fin M) ℂ :=
  inverseFourierMatrix M * eigenphaseDiagonal M φ * star (inverseFourierMatrix M)

theorem coherentPhasePreparation_unitary (M : ℕ) (φ : ℝ) (hM : 0 < M) :
    coherentPhasePreparation M φ ∈ Matrix.unitaryGroup (Fin M) ℂ := by
  have hF := inverseFourierMatrix_unitary M hM
  exact (Matrix.unitaryGroup (Fin M) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin M) ℂ).mul_mem hF (eigenphaseDiagonal_unitary M φ))
    (unitary.star_mem hF)

/-- The concrete phase-preparation zero column is the Appendix B amplitude. -/
theorem coherentPhasePreparation_zero_column (M : ℕ) (φ : ℝ) (hM : 0 < M)
    (j : Fin M) :
    coherentPhasePreparation M φ j ⟨0, hM⟩ = phaseEstAmplitude M φ j := by
  unfold coherentPhasePreparation
  rw [Matrix.mul_apply]
  simp only [eigenphaseDiagonal, Matrix.mul_diagonal, Matrix.star_apply, Complex.star_def,
    inverseFourierMatrix, Fin.coe_ofNat_eq_mod, Nat.zero_mod, Nat.cast_zero, zero_div, sub_zero, mul_zero,
    Complex.exp_zero, mul_one, Complex.conj_ofReal]
  unfold phaseEstAmplitude
  rw [← Fin.sum_univ_eq_sum_range]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ((((Real.sqrt M)⁻¹ : ℝ) : ℂ) ^ 2) *
        (Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * (0 - (j : ℂ) / M)) *
          Complex.exp (2 * Real.pi * Complex.I * (r : ℂ) * φ)) := by ring
    _ = _ := by
      rw [fourier_normalization M hM, ← Complex.exp_add]
      congr 2
      push_cast
      ring

/-- Equation (16) with the explicit phase-estimation probabilities and actual
unitary rotations, followed by inverse phase estimation. -/
theorem coherentPhaseFilter_amplitude (M : ℕ) (φ : ℝ) (hM : 0 < M) (g : Fin M → ℝ) :
    phaseUncompute (coherentPhasePreparation M φ) g (⟨0, hM⟩, 0) (⟨0, hM⟩, 0) =
      ((∑ j, phaseEstProb M φ j * g j : ℝ) : ℂ) := by
  rw [phaseUncompute_amplitude]
  simp only [coherentPhasePreparation_zero_column M φ hM, phaseEstProb]

section FullspacePreparation

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Coherent multiplexing between two arbitrary changes of selector basis. -/
def sandwichSelect {s : Type*} [Fintype s] [DecidableEq s]
    (A B : Matrix s s ℂ) (K : s → Matrix n n ℂ) : Matrix (s × n) (s × n) ℂ :=
  Matrix.kronecker A (1 : Matrix n n ℂ) * selectMatrix K *
    Matrix.kronecker B (1 : Matrix n n ℂ)

lemma sandwichSelect_block {s : Type*} [Fintype s] [DecidableEq s]
    (A B : Matrix s s ℂ) (K : s → Matrix n n ℂ) (q r : s) :
    (sandwichSelect A B K).submatrix (fun i => (q, i)) (fun i => (r, i)) =
      ∑ j, (A q j * B j r) • K j := by
  ext a b
  simp [sandwichSelect, selectMatrix, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker, Matrix.kronecker_apply, Matrix.one_apply, Matrix.sum_apply,
    Matrix.smul_apply, apply_ite, mul_assoc, mul_comm, mul_left_comm]

/-- Actual full-space phase estimation: inverse Fourier, controlled powers of
V, and Fourier.  Its definition never uses an eigenbasis. -/
def phaseEstimationMatrix (V : Matrix n n ℂ) (M : ℕ) :
    Matrix (Fin M × n) (Fin M × n) ℂ :=
  sandwichSelect (inverseFourierMatrix M) (star (inverseFourierMatrix M))
    (fun r => V ^ r.val)

theorem phaseEstimationMatrix_unitary (V : Matrix n n ℂ)
    (hV : V ∈ Matrix.unitaryGroup n ℂ) (M : ℕ) (hM : 0 < M) :
    phaseEstimationMatrix V M ∈ Matrix.unitaryGroup (Fin M × n) ℂ := by
  have hF := inverseFourierMatrix_unitary M hM
  have hI := (Matrix.unitaryGroup n ℂ).one_mem
  have hL := Matrix.kronecker_mem_unitary hF hI
  have hR := Matrix.kronecker_mem_unitary (unitary.star_mem hF) hI
  have hK := selectMatrix_unitary (fun r : Fin M => V ^ r.val)
    (fun r => (Matrix.unitaryGroup n ℂ).pow_mem hV r.val)
  exact (Matrix.unitaryGroup (Fin M × n) ℂ).mul_mem
    ((Matrix.unitaryGroup (Fin M × n) ℂ).mul_mem hL hK) hR

lemma phaseEstimationMatrix_block (V : Matrix n n ℂ) (M : ℕ) (hM : 0 < M)
    (j : Fin M) :
    (phaseEstimationMatrix V M).submatrix (fun i => (j, i)) (fun i => (⟨0, hM⟩, i)) =
      ∑ r : Fin M, (inverseFourierMatrix M j r *
        conj (inverseFourierMatrix M ⟨0, hM⟩ r)) • V ^ r.val := by
  rw [phaseEstimationMatrix, sandwichSelect_block]
  rfl

end FullspacePreparation

end Paper25
