import Paper26.SpectralLoss
import Paper26.Normalization
import Paper26.ShellAccounting
import Mathlib.Analysis.Complex.Order

/-!
# Lemma 5.4 in the original matrix basis

The estimate is an arbitrary positive-semidefinite, trace-one complex matrix.
Its spectral theorem, rather than a diagonal-matrix hypothesis, supplies the
basis in which the already-proved finite weighted estimate is applied. The
conclusion uses the actual nonsingular inverse of the regularized output.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder

namespace Paper26.Regularization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Isotropic regularization in the original basis. Real coefficients are
embedded into the complex matrix scalar field. -/
def regularize (α : ℝ) (ρhat : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  (((1 - α : ℝ) : ℂ)) • ρhat + (((α / (Fintype.card ι : ℝ) : ℝ) : ℂ)) • 1

/-- Regularization is automatically strictly positive. -/
theorem regularize_posDef [Nonempty ι] (ρhat : Matrix ι ι ℂ)
    (hhat : ρhat.PosSemidef) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    (regularize α ρhat).PosDef := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hfirst : ((((1 - α : ℝ) : ℂ)) • ρhat).PosSemidef :=
    hhat.smul (show (0 : ℂ) ≤ ((1 - α : ℝ) : ℂ) from
      Complex.nonneg_iff.mpr ⟨by simpa using (show 0 ≤ 1 - α by linarith), by simp⟩)
  have hsecond : ((((α / (Fintype.card ι : ℝ) : ℝ) : ℂ)) •
      (1 : Matrix ι ι ℂ)).PosDef :=
    Matrix.PosDef.one.smul (show (0 : ℂ) < ((α / (Fintype.card ι : ℝ) : ℝ) : ℂ) from
      Complex.pos_iff.mpr ⟨by simpa using div_pos hα hd, by simp⟩)
  exact Matrix.PosDef.posSemidef_add hfirst hsecond

/-- The spectral representation is obtained from the actual density estimate. -/
theorem exists_density_spectral_representation (ρhat : Matrix ι ι ℂ)
    (hhat : ρhat.PosSemidef) (htrace : Matrix.trace ρhat = 1) :
    ∃ (U : Matrix ι ι ℂ) (p : ι → ℝ),
      Uᴴ * U = 1 ∧ U * Uᴴ = 1 ∧ (∀ i, 0 ≤ p i) ∧ (∑ i, p i = 1) ∧
      ρhat = Normalization.conjugate U (Normalization.diagonalMatrix p) := by
  let U : Matrix ι ι ℂ := hhat.1.eigenvectorUnitary
  let p : ι → ℝ := hhat.1.eigenvalues
  have hU₁ : Uᴴ * U = 1 := by
    simpa only [U, unitary.coe_star, Matrix.star_eq_conjTranspose] using
      unitary.coe_star_mul_self hhat.1.eigenvectorUnitary
  have hU₂ : U * Uᴴ = 1 := by
    simpa only [U, unitary.coe_star, Matrix.star_eq_conjTranspose] using
      unitary.coe_mul_star_self hhat.1.eigenvectorUnitary
  have heq : ρhat = Normalization.conjugate U (Normalization.diagonalMatrix p) := by
    simpa only [U, p, Normalization.conjugate, Normalization.diagonalMatrix,
      Function.comp_def, Matrix.star_eq_conjTranspose] using hhat.1.spectral_theorem
  have hsum : ∑ i, p i = 1 := by
    have ht := Normalization.trace_conjugate_diagonal U p hU₁
    rw [← heq, htrace] at ht
    simpa using ht.symm
  exact ⟨U, p, hU₁, hU₂, hhat.eigenvalues_nonneg, hsum, heq⟩

/-- The spectrum of the original-basis regularization has the stated formula. -/
theorem diagonal_regularized (α : ℝ) (p : ι → ℝ) :
    Normalization.diagonalMatrix (SpectralLoss.regularizedSpectrum α p) =
      (((1 - α : ℝ) : ℂ)) • Normalization.diagonalMatrix p +
        (((α / (Fintype.card ι : ℝ) : ℝ) : ℂ)) • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Normalization.diagonalMatrix, SpectralLoss.regularizedSpectrum,
      Complex.ofReal_add, Complex.ofReal_mul]
  · simp [Normalization.diagonalMatrix, Matrix.diagonal, hij]

theorem regularize_conjugate (U : Matrix ι ι ℂ) (p : ι → ℝ) (α : ℝ)
    (hU : U * Uᴴ = 1) :
    regularize α (Normalization.conjugate U (Normalization.diagonalMatrix p)) =
      Normalization.conjugate U
        (Normalization.diagonalMatrix (SpectralLoss.regularizedSpectrum α p)) := by
  rw [diagonal_regularized, Normalization.conjugate_add,
    Normalization.conjugate_smul, Normalization.conjugate_smul]
  simp [regularize, Normalization.conjugate, hU]

/-- Trace one is preserved by isotropic regularization. -/
theorem regularize_trace_one [Nonempty ι] (ρhat : Matrix ι ι ℂ)
    (hhat : ρhat.PosSemidef) (htrace : Matrix.trace ρhat = 1) (α : ℝ) :
    Matrix.trace (regularize α ρhat) = 1 := by
  obtain ⟨U, p, hU₁, hU₂, hp, hsum, heq⟩ :=
    exists_density_spectral_representation ρhat hhat htrace
  rw [heq, regularize_conjugate U p α hU₂, Normalization.trace_conjugate U _ hU₁]
  simp only [Normalization.diagonalMatrix, Matrix.trace_diagonal, ← Complex.ofReal_sum,
    SpectralLoss.regularizedSpectrum_sum hsum, Complex.ofReal_one]

omit [DecidableEq ι] in
/-- Bridge between the two explicit entrywise Frobenius-square conventions. -/
theorem frobeniusSq_eq_entryNorm (E : Matrix ι ι ℂ) :
    SpectralLoss.frobeniusSq E = ShellAccounting.frobeniusSq E := by
  simp only [SpectralLoss.frobeniusSq, ShellAccounting.frobeniusSq, Complex.sq_norm]

/-- No unitary change of basis changes the actual Frobenius error. -/
theorem frobeniusSq_coordinates (U E : Matrix ι ι ℂ) (hU : U * Uᴴ = 1) :
    SpectralLoss.frobeniusSq (Normalization.coordinates U E) =
      SpectralLoss.frobeniusSq E := by
  simp only [frobeniusSq_eq_entryNorm, Normalization.coordinates]
  rw [ShellAccounting.frobeniusSq_mul_unitary _ U hU,
    ShellAccounting.frobeniusSq_unitary_mul E Uᴴ (by simpa using hU)]

/-- The weighted sum used in the normalization module is the same right-inverse
spectral error, with the complete noncommuting matrix entries retained. -/
theorem rightEnergy_eq_spectral (ρ : Matrix ι ι ℂ) (a : ι → ℝ) :
    Normalization.rightEnergy ρ a = SpectralLoss.rightInverse a
      (ρ - Normalization.diagonalMatrix a) := by
  simp [Normalization.rightEnergy, Normalization.spectralEnergy,
    SpectralLoss.rightInverse, Matrix.sub_apply, div_eq_mul_inv, mul_comm]

/-- The actual nonsingular-inverse trace loss equals the full spectral sum in
any unitary eigenbasis of its positive output. -/
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

/-- Equation (47), for an arbitrary density estimate in the original matrix
basis. The left side uses the actual matrix inverse, not a supplied eigenbasis
or an assumed spectral loss. -/
theorem regularization_bound [Nonempty ι] (ρ ρhat : Matrix ι ι ℂ)
    (hρ : ρ.IsHermitian) (hhat : ρhat.PosSemidef)
    (htrace : Matrix.trace ρhat = 1) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    (Matrix.trace ((ρ - regularize α ρhat) * (ρ - regularize α ρhat) *
      (regularize α ρhat)⁻¹)).re ≤
      (2 * (Fintype.card ι : ℝ) / α) * SpectralLoss.frobeniusSq (ρ - ρhat) +
        2 * α / (1 - α) := by
  obtain ⟨U, p, hU₁, hU₂, hp, hsum, heq⟩ :=
    exists_density_spectral_representation ρhat hhat htrace
  have hσ : regularize α ρhat = Normalization.conjugate U
      (Normalization.diagonalMatrix (SpectralLoss.regularizedSpectrum α p)) := by
    rw [heq, regularize_conjugate U p α hU₂]
  have hfrob : SpectralLoss.frobeniusSq
      (Normalization.coordinates U ρ - Normalization.diagonalMatrix p) =
      SpectralLoss.frobeniusSq (ρ - ρhat) := by
    have hcoord : Normalization.coordinates U (ρ - ρhat) =
        Normalization.coordinates U ρ - Normalization.diagonalMatrix p := by
      rw [Normalization.coordinates_sub, heq, Normalization.coordinates_conjugate U _ hU₁]
    rw [← hcoord, frobeniusSq_coordinates U _ hU₂]
  have hs := SpectralLoss.regularization_bound hα hα1 hp hsum
    (Normalization.coordinates U ρ)
  change Normalization.standardRightEnergy ρ (regularize α ρhat) ≤ _
  rw [hσ, standardRightEnergy_spectral U ρ _ hU₁ hU₂ hρ
    (SpectralLoss.regularizedSpectrum_pos hα hα1 hp)]
  rw [← hfrob]
  exact hs

/-- The epsilon/8 specialization of Lemma 5.4, still using the original-basis
trace and actual inverse. -/
theorem regularization_epsilon [Nonempty ι] (ρ ρhat : Matrix ι ι ℂ)
    (hρ : ρ.IsHermitian) (hhat : ρhat.PosSemidef) (htrace : Matrix.trace ρhat = 1)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (herr : SpectralLoss.frobeniusSq (ρ - ρhat) ≤
      ε ^ 2 / (64 * (Fintype.card ι : ℝ))) :
    (Matrix.trace ((ρ - regularize (ε / 8) ρhat) * (ρ - regularize (ε / 8) ρhat) *
      (regularize (ε / 8) ρhat)⁻¹)).re ≤ ε := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hα : 0 < ε / 8 := by positivity
  have hα1 : ε / 8 < 1 := by linarith
  have hbound := regularization_bound ρ ρhat hρ hhat htrace hα hα1
  have hmult := mul_le_mul_of_nonneg_left herr
    (by positivity : 0 ≤ 2 * (Fintype.card ι : ℝ) / (ε / 8))
  have heq : (2 * (Fintype.card ι : ℝ) / (ε / 8)) *
      (ε ^ 2 / (64 * (Fintype.card ι : ℝ))) = ε / 4 := by
    field_simp [ne_of_gt hε, ne_of_gt hd]
    ring
  rw [heq] at hmult
  have hrest : 2 * (ε / 8) / (1 - ε / 8) ≤ ε / 2 := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - ε / 8)).mpr
    nlinarith
  linarith

end Paper26.Regularization
