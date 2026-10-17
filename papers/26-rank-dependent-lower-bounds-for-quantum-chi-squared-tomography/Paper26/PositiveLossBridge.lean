import Paper26.QuantumModel
import Paper26.Normalization
import Paper26.TailConvexity

/-!
# Intrinsic trace formulas for the actual positive-output quantum losses

The selected spectral basis is taken from `QuantumModel.Density.eigenbasis`.
No ordering or uniqueness property of eigenvectors is assumed. The resulting
trace formulas use the actual inverse-Jordan operator and actual matrix inverse.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal

namespace Paper26.PositiveLossBridge

open QuantumModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma unitary_left (U : Matrix.unitaryGroup ι ℂ) :
    (U : Matrix ι ι ℂ)ᴴ * (U : Matrix ι ι ℂ) = 1 := by
  simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose] using
    unitary.coe_star_mul_self U

lemma unitary_right (U : Matrix.unitaryGroup ι ℂ) :
    (U : Matrix ι ι ℂ) * (U : Matrix ι ι ℂ)ᴴ = 1 := by
  simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose] using
    unitary.coe_mul_star_self U

/-- The actual eigenbasis selected by the quantum model reconstructs the
output in the normalization module's matrix notation. -/
theorem density_spectral_reconstruction (σ : Density ι) :
    σ.matrix = Normalization.conjugate (σ.eigenbasis : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix σ.spectrum) := by
  simpa only [Normalization.conjugate, Normalization.diagonalMatrix,
    Matrix.star_eq_conjTranspose] using σ.spectral_decomposition

/-- The quantum model's complete difference matrix is exactly the true state
in the selected output basis minus the output's diagonal spectrum. -/
theorem eigenDifference_eq_coordinates (ρ σ : Density ι) :
    eigenDifference ρ σ =
      Normalization.coordinates (σ.eigenbasis : Matrix ι ι ℂ) ρ.matrix -
        Normalization.diagonalMatrix σ.spectrum := by
  have hd : Normalization.coordinates (σ.eigenbasis : Matrix ι ι ℂ) σ.matrix =
      Normalization.diagonalMatrix σ.spectrum := by
    simpa only [Normalization.coordinates, Normalization.diagonalMatrix,
      Matrix.star_eq_conjTranspose] using σ.diagonal_in_eigenbasis
  calc
    _ = Normalization.coordinates (σ.eigenbasis : Matrix ι ι ℂ)
        (ρ.matrix - σ.matrix) := by
      simp only [eigenDifference, Normalization.coordinates, Matrix.star_eq_conjTranspose]
    _ = _ := by rw [Normalization.coordinates_sub, hd]

lemma buresEnergy_eq_spectral (ρ : Matrix ι ι ℂ) (a : ι → ℝ) :
    Normalization.buresEnergy ρ a = SpectralLoss.bures a
      (ρ - Normalization.diagonalMatrix a) := by
  unfold Normalization.buresEnergy Normalization.spectralEnergy SpectralLoss.bures
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  simp only [Matrix.sub_apply]
  ring

lemma rightEnergy_eq_spectral (ρ : Matrix ι ι ℂ) (a : ι → ℝ) :
    Normalization.rightEnergy ρ a = SpectralLoss.rightInverse a
      (ρ - Normalization.diagonalMatrix a) := by
  simp [Normalization.rightEnergy, Normalization.spectralEnergy,
    SpectralLoss.rightInverse, Matrix.sub_apply, div_eq_mul_inv, mul_comm]

/-- The intrinsic Bures trace formula in any positive spectral representation. -/
theorem standardBuresEnergy_spectral (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1)
    (hρ : ρ.IsHermitian) (ha : ∀ i, 0 < a i) :
    Normalization.standardBuresEnergy ρ
        (Normalization.conjugate U (Normalization.diagonalMatrix a)) =
      SpectralLoss.bures a
        (Normalization.coordinates U ρ - Normalization.diagonalMatrix a) := by
  rw [← Normalization.matrixBuresEnergy_standard U ρ a hU₁ hU₂ ha,
    Normalization.matrixBuresEnergy_coordinates U ρ a hU₁ hU₂ hρ.eq,
    buresEnergy_eq_spectral]

/-- The actual inverse-matrix trace formula in any positive spectral representation. -/
theorem standardRightEnergy_spectral (U ρ : Matrix ι ι ℂ) (a : ι → ℝ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1)
    (hρ : ρ.IsHermitian) (ha : ∀ i, 0 < a i) :
    Normalization.standardRightEnergy ρ
        (Normalization.conjugate U (Normalization.diagonalMatrix a)) =
      SpectralLoss.rightInverse a
        (Normalization.coordinates U ρ - Normalization.diagonalMatrix a) := by
  rw [← Normalization.matrixRightEnergy_standard U ρ a hU₁ hU₂ ha,
    Normalization.matrixRightEnergy_coordinates U ρ a hU₁ hU₂ hρ.eq,
    rightEnergy_eq_spectral]

/-- Actual `QuantumModel.chiB`, for positive definite output, equals the
intrinsic inverse-Jordan trace loss in the original matrix basis. -/
theorem chiB_eq_standardBuresEnergy (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    chiB ρ σ = ENNReal.ofReal
      (Normalization.standardBuresEnergy ρ.matrix σ.matrix) := by
  rw [chiB_eq_of_posDef ρ σ hσ, eigenDifference_eq_coordinates,
    ← standardBuresEnergy_spectral (σ.eigenbasis : Matrix ι ι ℂ) ρ.matrix σ.spectrum
      (unitary_left σ.eigenbasis) (unitary_right σ.eigenbasis) ρ.hermitian
      (σ.spectrum_pos hσ),
    ← density_spectral_reconstruction σ]

/-- Actual `QuantumModel.chiR`, for positive definite output, equals the trace
loss using the output's actual nonsingular inverse. -/
theorem chiR_eq_standardRightEnergy (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    chiR ρ σ = ENNReal.ofReal
      (Normalization.standardRightEnergy ρ.matrix σ.matrix) := by
  rw [chiR_eq_of_posDef ρ σ hσ, eigenDifference_eq_coordinates,
    ← standardRightEnergy_spectral (σ.eigenbasis : Matrix ι ι ℂ) ρ.matrix σ.spectrum
      (unitary_left σ.eigenbasis) (unitary_right σ.eigenbasis) ρ.hermitian
      (σ.spectrum_pos hσ),
    ← density_spectral_reconstruction σ]


/-- The intrinsic Bures trace is nonnegative on genuine states with positive
output, so the `ofReal` bridge loses no real-valued information. -/
theorem standardBuresEnergy_nonneg (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    0 ≤ Normalization.standardBuresEnergy ρ.matrix σ.matrix := by
  rw [density_spectral_reconstruction σ,
    standardBuresEnergy_spectral (σ.eigenbasis : Matrix ι ι ℂ) ρ.matrix σ.spectrum
      (unitary_left σ.eigenbasis) (unitary_right σ.eigenbasis) ρ.hermitian
      (σ.spectrum_pos hσ)]
  exact SpectralLoss.bures_nonneg (σ.spectrum_pos hσ) _

theorem standardRightEnergy_nonneg (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    0 ≤ Normalization.standardRightEnergy ρ.matrix σ.matrix := by
  rw [density_spectral_reconstruction σ,
    standardRightEnergy_spectral (σ.eigenbasis : Matrix ι ι ℂ) ρ.matrix σ.spectrum
      (unitary_left σ.eigenbasis) (unitary_right σ.eigenbasis) ρ.hermitian
      (σ.spectrum_pos hσ)]
  exact SpectralLoss.rightInverse_nonneg (σ.spectrum_pos hσ) _

theorem chiB_toReal_standard (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    (chiB ρ σ).toReal = Normalization.standardBuresEnergy ρ.matrix σ.matrix := by
  rw [chiB_eq_standardBuresEnergy ρ σ hσ,
    ENNReal.toReal_ofReal (standardBuresEnergy_nonneg ρ σ hσ)]

theorem chiR_toReal_standard (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    (chiR ρ σ).toReal = Normalization.standardRightEnergy ρ.matrix σ.matrix := by
  rw [chiR_eq_standardRightEnergy ρ σ hσ,
    ENNReal.toReal_ofReal (standardRightEnergy_nonneg ρ σ hσ)]

/-- Actual unitary conjugation preserves positivity and trace one and hence
produces an actual `QuantumModel.Density`. -/
def conjugateDensity (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) : Density ι where
  matrix := Normalization.conjugate (U : Matrix ι ι ℂ) ρ.matrix
  positive := ρ.positive.mul_mul_conjTranspose_same (U : Matrix ι ι ℂ)
  trace_one := by
    rw [Normalization.trace_conjugate _ _ (unitary_left U), ρ.trace_one]

@[simp] theorem conjugateDensity_matrix (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) :
    (conjugateDensity U ρ).matrix =
      Normalization.conjugate (U : Matrix ι ι ℂ) ρ.matrix := rfl

theorem conjugateDensity_posDef (U : Matrix.unitaryGroup ι ℂ) (σ : Density ι)
    (hσ : σ.matrix.PosDef) : (conjugateDensity U σ).matrix.PosDef :=
  TailConvexity.conjugate_posDef (U : Matrix ι ι ℂ) σ.matrix (unitary_right U) hσ

/-- The positive inverse-Jordan trace loss is unchanged by simultaneous unitary
conjugation in the original matrix basis. -/
theorem standardBuresEnergy_conjugate (U ρ A : Matrix ι ι ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) (hA : A.PosDef) :
    Normalization.standardBuresEnergy (Normalization.conjugate U ρ)
      (Normalization.conjugate U A) = Normalization.standardBuresEnergy ρ A := by
  change TailConvexity.Q (Normalization.conjugate U A)
      (Normalization.conjugate U ρ - Normalization.conjugate U A) =
    TailConvexity.Q A (ρ - A)
  rw [← Normalization.conjugate_sub U ρ A]
  exact TailConvexity.Q_conjugate U A (ρ - A) hU₁ hU₂ hA

/-- The actual inverse of a positive matrix is equivariant under unitary
conjugation. The proof verifies a right inverse and uses inverse uniqueness. -/
theorem inverse_conjugate (U A : Matrix ι ι ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) (hA : A.PosDef) :
    (Normalization.conjugate U A)⁻¹ = Normalization.conjugate U A⁻¹ := by
  apply Matrix.inv_eq_right_inv
  rw [← Normalization.conjugate_mul U A A⁻¹ hU₁,
    Matrix.mul_nonsing_inv A ((Matrix.isUnit_iff_isUnit_det A).mp hA.isUnit)]
  simpa only [Normalization.conjugate, Matrix.mul_one] using hU₂

/-- The right-inverse trace loss uses the actual inverse after conjugation. -/
theorem standardRightEnergy_conjugate (U ρ A : Matrix ι ι ℂ)
    (hU₁ : Uᴴ * U = 1) (hU₂ : U * Uᴴ = 1) (hA : A.PosDef) :
    Normalization.standardRightEnergy (Normalization.conjugate U ρ)
      (Normalization.conjugate U A) = Normalization.standardRightEnergy ρ A := by
  unfold Normalization.standardRightEnergy
  simp only [← Normalization.conjugate_sub U ρ A]
  rw [inverse_conjugate U A hU₁ hU₂ hA,
    ← Normalization.conjugate_mul U (ρ - A) (ρ - A) hU₁,
    ← Normalization.conjugate_mul U ((ρ - A) * (ρ - A)) A⁻¹ hU₁,
    Normalization.trace_conjugate U _ hU₁]

/-- Actual quantum Bures chi-squared is invariant under simultaneous unitary
conjugation whenever the output is positive definite. -/
theorem chiB_unitary (U : Matrix.unitaryGroup ι ℂ) (ρ σ : Density ι)
    (hσ : σ.matrix.PosDef) :
    chiB (conjugateDensity U ρ) (conjugateDensity U σ) = chiB ρ σ := by
  rw [chiB_eq_standardBuresEnergy _ _ (conjugateDensity_posDef U σ hσ),
    chiB_eq_standardBuresEnergy ρ σ hσ, conjugateDensity_matrix,
    conjugateDensity_matrix,
    standardBuresEnergy_conjugate (U : Matrix ι ι ℂ) ρ.matrix σ.matrix
      (unitary_left U) (unitary_right U) hσ]

/-- Actual quantum right-inverse chi-squared is invariant under simultaneous
unitary conjugation whenever the output is positive definite. -/
theorem chiR_unitary (U : Matrix.unitaryGroup ι ℂ) (ρ σ : Density ι)
    (hσ : σ.matrix.PosDef) :
    chiR (conjugateDensity U ρ) (conjugateDensity U σ) = chiR ρ σ := by
  rw [chiR_eq_standardRightEnergy _ _ (conjugateDensity_posDef U σ hσ),
    chiR_eq_standardRightEnergy ρ σ hσ, conjugateDensity_matrix,
    conjugateDensity_matrix,
    standardRightEnergy_conjugate (U : Matrix ι ι ℂ) ρ.matrix σ.matrix
      (unitary_left U) (unitary_right U) hσ]

omit [Fintype ι] in
lemma diagonal_difference (p q : ι → ℝ) :
    Normalization.diagonalMatrix p - Normalization.diagonalMatrix q =
      SpectralLoss.diagonalDifference p q := by
  simp only [Normalization.diagonalMatrix, Matrix.diagonal_sub,
    SpectralLoss.diagonalDifference, Complex.ofReal_sub]

/-- Intrinsic Bures energy on real diagonal matrices is the classical
chi-squared sum, obtained using the identity basis in the trace bridge. -/
theorem standardBuresEnergy_diagonal (p q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    Normalization.standardBuresEnergy (Normalization.diagonalMatrix p)
      (Normalization.diagonalMatrix q) = SpectralLoss.classical p q := by
  have h := standardBuresEnergy_spectral (1 : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix p) q (by simp) (by simp)
    (Normalization.diagonalMatrix_conjTranspose p) hq
  simp only [Normalization.conjugate, Normalization.coordinates,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
  rw [diagonal_difference p q, SpectralLoss.bures_diagonal hq] at h
  exact h

theorem standardRightEnergy_diagonal (p q : ι → ℝ) (hq : ∀ i, 0 < q i) :
    Normalization.standardRightEnergy (Normalization.diagonalMatrix p)
      (Normalization.diagonalMatrix q) = SpectralLoss.classical p q := by
  have h := standardRightEnergy_spectral (1 : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix p) q (by simp) (by simp)
    (Normalization.diagonalMatrix_conjTranspose p) hq
  simp only [Normalization.conjugate, Normalization.coordinates,
    Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one] at h
  rw [diagonal_difference p q, SpectralLoss.rightInverse_diagonal p q] at h
  exact h

/-- Actual quantum Bures loss of diagonal density matrices equals the classical
sum, independently of whatever eigenbasis the quantum model selected. -/
theorem chiB_diagonal (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (hqSum : ∑ i, q i = 1) (hqpos : ∀ i, 0 < q i) :
    chiB (Density.diagonal p hp hpSum) (Density.diagonal q hq hqSum) =
      ENNReal.ofReal (SpectralLoss.classical p q) := by
  rw [chiB_eq_standardBuresEnergy _ _ (Density.diagonal_posDef q hq hqSum hqpos)]
  change ENNReal.ofReal (Normalization.standardBuresEnergy
    (Normalization.diagonalMatrix p) (Normalization.diagonalMatrix q)) = _
  rw [standardBuresEnergy_diagonal p q hqpos]

/-- The same basis-independent classical reduction for actual right-inverse
quantum chi-squared loss. -/
theorem chiR_diagonal (p q : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (hqSum : ∑ i, q i = 1) (hqpos : ∀ i, 0 < q i) :
    chiR (Density.diagonal p hp hpSum) (Density.diagonal q hq hqSum) =
      ENNReal.ofReal (SpectralLoss.classical p q) := by
  rw [chiR_eq_standardRightEnergy _ _ (Density.diagonal_posDef q hq hqSum hqpos)]
  change ENNReal.ofReal (Normalization.standardRightEnergy
    (Normalization.diagonalMatrix p) (Normalization.diagonalMatrix q)) = _
  rw [standardRightEnergy_diagonal p q hqpos]

end Paper26.PositiveLossBridge
