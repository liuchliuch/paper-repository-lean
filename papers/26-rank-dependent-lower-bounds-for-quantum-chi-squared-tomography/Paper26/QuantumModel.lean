import Paper26.SpectralLoss
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Trace
import Mathlib.Data.ENNReal.Real

/-!
# Finite dimensional states and quantum chi-squared losses

The ambient matrices are complex matrices, rather than an abstract scalar surrogate.
A density matrix is positive semidefinite with trace one. The losses use the
actual eigenvectors of the output matrix. For a singular output the finite sum
is restricted to its positive spectral support, and the loss is infinity when
the input support is not contained in that output support.

This file does not define continuous or adaptive quantum experiments.
-/

namespace Paper26.QuantumModel

open scoped BigOperators ComplexOrder Matrix ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A density matrix on the complex Hilbert space indexed by `ι`. -/
structure Density (ι : Type*) [Fintype ι] where
  matrix : Matrix ι ι ℂ
  positive : matrix.PosSemidef
  trace_one : Matrix.trace matrix = 1

namespace Density

omit [DecidableEq ι] in
theorem hermitian (ρ : Density ι) : ρ.matrix.IsHermitian := ρ.positive.isHermitian

/-- The actual matrix rank bound, with unrestricted density-matrix outputs. -/
def RankAtMost (r : ℕ) : Set (Density ι) := {ρ | ρ.matrix.rank ≤ r}

/-- Eigenvalues selected by the finite-dimensional spectral theorem. -/
def spectrum (σ : Density ι) : ι → ℝ := σ.hermitian.eigenvalues

/-- Columns are the orthonormal eigenvectors of the output state. -/
def eigenbasis (σ : Density ι) : Matrix.unitaryGroup ι ℂ :=
  σ.hermitian.eigenvectorUnitary

theorem spectrum_nonneg (σ : Density ι) (i : ι) : 0 ≤ σ.spectrum i :=
  σ.positive.eigenvalues_nonneg i

theorem spectrum_sum (σ : Density ι) : ∑ i, σ.spectrum i = 1 := by
  have h := σ.hermitian.trace_eq_sum_eigenvalues
  rw [σ.trace_one] at h
  have hh := congrArg Complex.re h
  simpa [spectrum] using hh.symm

theorem spectral_decomposition (σ : Density ι) :
    σ.matrix = (σ.eigenbasis : Matrix ι ι ℂ) *
      Matrix.diagonal (fun i => (σ.spectrum i : ℂ)) *
      star (σ.eigenbasis : Matrix ι ι ℂ) := by
  simpa [eigenbasis, spectrum, Function.comp_def] using σ.hermitian.spectral_theorem

theorem diagonal_in_eigenbasis (σ : Density ι) :
    star (σ.eigenbasis : Matrix ι ι ℂ) * σ.matrix *
      (σ.eigenbasis : Matrix ι ι ℂ) =
      Matrix.diagonal (fun i => (σ.spectrum i : ℂ)) := by
  simpa [eigenbasis, spectrum, Function.comp_def] using
    σ.hermitian.star_mul_self_mul_eq_diagonal

/-- A positive definite output has no zero eigenvalues. -/
theorem spectrum_pos {σ : Density ι} (hσ : σ.matrix.PosDef) (i : ι) :
    0 < σ.spectrum i := hσ.eigenvalues_pos i


/-- Embed a classical probability vector as an actual diagonal density matrix. -/
def diagonal (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) : Density ι where
  matrix := Matrix.diagonal (fun i => (p i : ℂ))
  positive := Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (hp i))
  trace_one := by
    rw [Matrix.trace_diagonal, ← Complex.ofReal_sum, hsum, Complex.ofReal_one]

@[simp] theorem diagonal_matrix (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1) :
    (diagonal p hp hsum).matrix = Matrix.diagonal (fun i => (p i : ℂ)) := rfl

theorem diagonal_posDef (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hppos : ∀ i, 0 < p i) : (diagonal p hp hsum).matrix.PosDef :=
  Matrix.posDef_diagonal_iff.mpr (fun i => RCLike.ofReal_pos.mpr (hppos i))

/-- Exact Frobenius squared difference for the classical embedding. -/
theorem frobeniusSq_diagonal_difference (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hpSum : ∑ i, p i = 1)
    (hq : ∀ i, 0 ≤ q i) (hqSum : ∑ i, q i = 1) :
    SpectralLoss.frobeniusSq ((diagonal p hp hpSum).matrix - (diagonal q hq hqSum).matrix) =
      ∑ i, (p i - q i) ^ 2 := by
  unfold SpectralLoss.frobeniusSq diagonal
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · simp [Complex.normSq_ofReal, ← Complex.ofReal_sub, pow_two]
  · intro j _ hji
    simp [Matrix.diagonal, Ne.symm hji]
  · simp

end Density

/-- An orthogonal projector is a self-adjoint idempotent complex matrix. -/
structure OrthogonalProjector (ι : Type*) [Fintype ι] where
  matrix : Matrix ι ι ℂ
  hermitian : matrix.IsHermitian
  idempotent : matrix * matrix = matrix

namespace OrthogonalProjector

omit [DecidableEq ι] in
theorem positive (P : OrthogonalProjector ι) : P.matrix.PosSemidef := by
  have h := Matrix.posSemidef_conjTranspose_mul_self P.matrix
  rwa [P.hermitian.eq, P.idempotent] at h

/-- The trace of an orthogonal projector is its actual matrix rank. -/
theorem trace_eq_rank (P : OrthogonalProjector ι) :
    Matrix.trace P.matrix = (P.matrix.rank : ℂ) := by
  have hid : IsIdempotentElem P.matrix.mulVecLin := by
    change P.matrix.mulVecLin.comp P.matrix.mulVecLin = P.matrix.mulVecLin
    rw [← Matrix.mulVecLin_mul, P.idempotent]
  have h := (LinearMap.IsIdempotentElem.isProj_range P.matrix.mulVecLin hid).trace
  simpa only [Matrix.rank, ← Matrix.toLin'_apply', Matrix.trace_toLin'_eq] using h

/-- The paper's flat state `P / r`, defined for a positive-rank projector. -/
def flat (P : OrthogonalProjector ι) (hr : 0 < P.matrix.rank) : Density ι where
  matrix := ((P.matrix.rank : ℝ)⁻¹) • P.matrix
  positive := P.positive.smul (inv_nonneg.mpr (Nat.cast_nonneg _))
  trace_one := by
    rw [Matrix.trace_smul, P.trace_eq_rank]
    simp only [Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_natCast]
    exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hr))

/-- Normalizing the projector does not change its column space or its rank. -/
theorem flat_rank (P : OrthogonalProjector ι) (hr : 0 < P.matrix.rank) :
    (P.flat hr).matrix.rank = P.matrix.rank := by
  have hc : ((P.matrix.rank : ℝ)⁻¹ : ℂ) ≠ 0 := by
    simp [Nat.ne_of_gt hr]
  have heq : (P.flat hr).matrix.mulVecLin =
      (((P.matrix.rank : ℝ)⁻¹ : ℂ)) • P.matrix.mulVecLin := by
    ext v i
    simp [flat, Complex.real_smul]
  unfold Matrix.rank
  rw [heq, LinearMap.range_smul _ _ hc]

theorem flat_mem_rankAtMost (P : OrthogonalProjector ι)
    (hr : 0 < P.matrix.rank) {r : ℕ} (hPr : P.matrix.rank ≤ r) :
    P.flat hr ∈ Density.RankAtMost r := by
  change (P.flat hr).matrix.rank ≤ r
  rwa [P.flat_rank hr]

end OrthogonalProjector

/-- `supp ρ ⊆ supp σ`, expressed invariantly as reverse kernel inclusion.
For Hermitian matrices the support is the orthogonal complement of the kernel. -/
def SupportContained (ρ σ : Density ι) : Prop :=
  ∀ v : ι → ℂ, σ.matrix *ᵥ v = 0 → ρ.matrix *ᵥ v = 0

omit [DecidableEq ι] in
theorem supportContained_refl (ρ : Density ι) : SupportContained ρ ρ :=
  fun _ h => h

theorem supportContained_of_posDef (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    SupportContained ρ σ := by
  intro v hv
  have hinj := Matrix.mulVec_injective_iff_isUnit.mpr hσ.isUnit
  have hz : v = 0 := hinj (hv.trans (Matrix.mulVec_zero σ.matrix).symm)
  simp [hz]

/-- The actual difference matrix in the selected eigenbasis of `σ`. -/
def eigenDifference (ρ σ : Density ι) : Matrix ι ι ℂ :=
  star (σ.eigenbasis : Matrix ι ι ℂ) * (ρ.matrix - σ.matrix) *
    (σ.eigenbasis : Matrix ι ι ℂ)

theorem eigenDifference_hermitian (ρ σ : Density ι) :
    (eigenDifference ρ σ).IsHermitian :=
  Matrix.isHermitian_conjTranspose_mul_mul _ (ρ.hermitian.sub σ.hermitian)

/-- The finite spectral support of `σ`. The denominators on this subtype are positive. -/
def SupportIndex (σ : Density ι) := {i : ι // 0 < σ.spectrum i}

instance (σ : Density ι) : Fintype (SupportIndex σ) := by
  classical
  unfold SupportIndex
  infer_instance

instance (σ : Density ι) : DecidableEq (SupportIndex σ) := Classical.decEq _

/-- Restriction of the transformed difference to the output's positive support. -/
def supportDifference (ρ σ : Density ι) : Matrix (SupportIndex σ) (SupportIndex σ) ℂ :=
  (eigenDifference ρ σ).submatrix Subtype.val Subtype.val

/-- The strictly positive eigenvalues of `σ` on its support. -/
def supportSpectrum (σ : Density ι) (i : SupportIndex σ) : ℝ := σ.spectrum i.val

theorem supportSpectrum_pos (σ : Density ι) (i : SupportIndex σ) :
    0 < supportSpectrum σ i := i.property

theorem supportDifference_hermitian (ρ σ : Density ι) :
    (supportDifference ρ σ).IsHermitian :=
  (eigenDifference_hermitian ρ σ).submatrix Subtype.val

/-- Bures/SLD chi-squared divergence, including the singular-output convention. -/
def chiB (ρ σ : Density ι) : ℝ≥0∞ := by
  classical
  exact if SupportContained ρ σ then
    ENNReal.ofReal (SpectralLoss.bures (supportSpectrum σ) (supportDifference ρ σ))
  else ∞

/-- Geometric chi-squared divergence, including the singular-output convention. -/
def chiG (ρ σ : Density ι) : ℝ≥0∞ := by
  classical
  exact if SupportContained ρ σ then
    ENNReal.ofReal (SpectralLoss.geometric (supportSpectrum σ) (supportDifference ρ σ))
  else ∞

/-- Right-inverse chi-squared divergence, including the singular-output convention. -/
def chiR (ρ σ : Density ι) : ℝ≥0∞ := by
  classical
  exact if SupportContained ρ σ then
    ENNReal.ofReal (SpectralLoss.rightInverse (supportSpectrum σ) (supportDifference ρ σ))
  else ∞

theorem chiB_eq_top_of_not_supportContained (ρ σ : Density ι)
    (h : ¬ SupportContained ρ σ) : chiB ρ σ = ∞ := by simp [chiB, h]

theorem chiG_eq_top_of_not_supportContained (ρ σ : Density ι)
    (h : ¬ SupportContained ρ σ) : chiG ρ σ = ∞ := by simp [chiG, h]

theorem chiR_eq_top_of_not_supportContained (ρ σ : Density ι)
    (h : ¬ SupportContained ρ σ) : chiR ρ σ = ∞ := by simp [chiR, h]

theorem chiB_ne_top_iff (ρ σ : Density ι) :
    chiB ρ σ ≠ ∞ ↔ SupportContained ρ σ := by
  classical
  by_cases h : SupportContained ρ σ <;> simp [chiB, h]

theorem chiG_ne_top_iff (ρ σ : Density ι) :
    chiG ρ σ ≠ ∞ ↔ SupportContained ρ σ := by
  classical
  by_cases h : SupportContained ρ σ <;> simp [chiG, h]

theorem chiR_ne_top_iff (ρ σ : Density ι) :
    chiR ρ σ ≠ ∞ ↔ SupportContained ρ σ := by
  classical
  by_cases h : SupportContained ρ σ <;> simp [chiR, h]

/-- Equation (5), now for actual density matrices and including singular outputs. -/
theorem loss_comparison (ρ σ : Density ι) :
    chiB ρ σ ≤ chiG ρ σ ∧ chiG ρ σ ≤ chiR ρ σ := by
  classical
  by_cases h : SupportContained ρ σ
  · simp only [chiB, chiG, chiR, if_pos h]
    exact ⟨ENNReal.ofReal_le_ofReal (SpectralLoss.bures_le_geometric
      (supportSpectrum_pos σ) (supportDifference ρ σ)),
      ENNReal.ofReal_le_ofReal (SpectralLoss.geometric_le_rightInverse
        (supportSpectrum_pos σ) (supportDifference_hermitian ρ σ))⟩
  · simp [chiB, chiG, chiR, h]


/-- No clipping is hidden by `ENNReal.ofReal`: the finite Bures sum is nonnegative. -/
theorem chiB_toReal (ρ σ : Density ι) (h : SupportContained ρ σ) :
    (chiB ρ σ).toReal =
      SpectralLoss.bures (supportSpectrum σ) (supportDifference ρ σ) := by
  simp only [chiB, if_pos h]
  exact ENNReal.toReal_ofReal (SpectralLoss.bures_nonneg
    (supportSpectrum_pos σ) (supportDifference ρ σ))

theorem chiG_toReal (ρ σ : Density ι) (h : SupportContained ρ σ) :
    (chiG ρ σ).toReal =
      SpectralLoss.geometric (supportSpectrum σ) (supportDifference ρ σ) := by
  simp only [chiG, if_pos h]
  exact ENNReal.toReal_ofReal (SpectralLoss.geometric_nonneg _ _)

theorem chiR_toReal (ρ σ : Density ι) (h : SupportContained ρ σ) :
    (chiR ρ σ).toReal =
      SpectralLoss.rightInverse (supportSpectrum σ) (supportDifference ρ σ) := by
  simp only [chiR, if_pos h]
  exact ENNReal.toReal_ofReal (SpectralLoss.rightInverse_nonneg
    (supportSpectrum_pos σ) (supportDifference ρ σ))

private theorem sum_support_eq_of_posDef {σ : Density ι} (hσ : σ.matrix.PosDef)
    (f : ι → ι → ℝ) :
    (∑ i : SupportIndex σ, ∑ j : SupportIndex σ, f i.val j.val) = ∑ i, ∑ j, f i j := by
  let e : SupportIndex σ ≃ ι := Equiv.subtypeUnivEquiv (σ.spectrum_pos hσ)
  apply Fintype.sum_equiv e
  intro i
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

/-- For a positive definite output this is exactly the full spectral sum in (3). -/
theorem chiB_eq_of_posDef (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    chiB ρ σ = ENNReal.ofReal (SpectralLoss.bures σ.spectrum (eigenDifference ρ σ)) := by
  simp only [chiB, if_pos (supportContained_of_posDef ρ σ hσ)]
  congr 1
  simpa only [SpectralLoss.bures, supportSpectrum, supportDifference, Matrix.submatrix_apply] using
    sum_support_eq_of_posDef hσ (fun i j => 2 * Complex.normSq (eigenDifference ρ σ i j) / (σ.spectrum i + σ.spectrum j))

theorem chiG_eq_of_posDef (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    chiG ρ σ = ENNReal.ofReal (SpectralLoss.geometric σ.spectrum (eigenDifference ρ σ)) := by
  simp only [chiG, if_pos (supportContained_of_posDef ρ σ hσ)]
  congr 1
  simpa only [SpectralLoss.geometric, supportSpectrum, supportDifference, Matrix.submatrix_apply] using
    sum_support_eq_of_posDef hσ (fun i j => Complex.normSq (eigenDifference ρ σ i j) / Real.sqrt (σ.spectrum i * σ.spectrum j))

/-- For a positive definite output this is exactly the full first sum in (4). -/
theorem chiR_eq_of_posDef (ρ σ : Density ι) (hσ : σ.matrix.PosDef) :
    chiR ρ σ = ENNReal.ofReal (SpectralLoss.rightInverse σ.spectrum (eigenDifference ρ σ)) := by
  simp only [chiR, if_pos (supportContained_of_posDef ρ σ hσ)]
  congr 1
  simpa only [SpectralLoss.rightInverse, supportSpectrum, supportDifference, Matrix.submatrix_apply] using
    sum_support_eq_of_posDef hσ (fun i j => Complex.normSq (eigenDifference ρ σ i j) / σ.spectrum j)

@[simp] theorem eigenDifference_self (σ : Density ι) : eigenDifference σ σ = 0 := by
  simp [eigenDifference]

@[simp] theorem supportDifference_self (σ : Density ι) : supportDifference σ σ = 0 := by
  simp [supportDifference]

@[simp] theorem chiB_self (σ : Density ι) : chiB σ σ = 0 := by
  simp [chiB, supportContained_refl, SpectralLoss.bures]

@[simp] theorem chiG_self (σ : Density ι) : chiG σ σ = 0 := by
  simp [chiG, supportContained_refl, SpectralLoss.geometric]

@[simp] theorem chiR_self (σ : Density ι) : chiR σ σ = 0 := by
  simp [chiR, supportContained_refl, SpectralLoss.rightInverse]


/-- Born's rule is nonnegative for a positive effect. -/
theorem trace_mul_effect_nonneg (ρ : Density ι) {E : Matrix ι ι ℂ}
    (hE : E.PosSemidef) : 0 ≤ (Matrix.trace (ρ.matrix * E)).re := by
  let U : Matrix ι ι ℂ := ρ.eigenbasis
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => (ρ.spectrum i : ℂ))
  let F := star U * E * U
  have hF : F.PosSemidef := hE.conjTranspose_mul_mul_same U
  have hdiag (i : ι) : 0 ≤ (F i i).re := by
    simpa only [← Pi.single_star, star_one, Matrix.mulVec_single_one,
      single_dotProduct, one_mul, Matrix.col_apply] using
      hF.re_dotProduct_nonneg (Pi.single i 1)
  have htrace : Matrix.trace (ρ.matrix * E) = Matrix.trace (D * F) := by
    calc
      _ = Matrix.trace (U * D * (star U * E)) := by
        rw [ρ.spectral_decomposition]
        simp only [U, D, Matrix.mul_assoc]
      _ = Matrix.trace (star U * E * U * D) := Matrix.trace_mul_cycle _ _ _
      _ = Matrix.trace (D * F) := Matrix.trace_mul_comm _ _
  rw [htrace]
  simp only [D, Matrix.trace, Matrix.diag_apply, Matrix.diagonal_mul, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (ρ.spectrum_nonneg i) (hdiag i)

/-- A finite-outcome POVM, with positive effects summing to the identity. -/
structure FinitePOVM (ι κ : Type*) [Fintype ι] [DecidableEq ι] [Fintype κ] where
  effect : κ → Matrix ι ι ℂ
  positive : ∀ y, (effect y).PosSemidef
  total : ∑ y, effect y = 1

namespace FinitePOVM

variable {κ : Type*} [Fintype κ]

/-- The real Born probability of each finite measurement outcome. -/
def born (M : FinitePOVM ι κ) (ρ : Density ι) (y : κ) : ℝ :=
  (Matrix.trace (ρ.matrix * M.effect y)).re

theorem born_nonneg (M : FinitePOVM ι κ) (ρ : Density ι) (y : κ) :
    0 ≤ M.born ρ y := trace_mul_effect_nonneg ρ (M.positive y)

theorem born_sum (M : FinitePOVM ι κ) (ρ : Density ι) : ∑ y, M.born ρ y = 1 := by
  classical
  simp only [born, ← Complex.re_sum, ← Matrix.trace_sum, ← Matrix.mul_sum,
    M.total, Matrix.mul_one, ρ.trace_one, Complex.one_re]

/-- Born's rule actually produces a normalized classical distribution. -/
theorem born_distribution (M : FinitePOVM ι κ) (ρ : Density ι) :
    (∀ y, 0 ≤ M.born ρ y) ∧ ∑ y, M.born ρ y = 1 :=
  ⟨M.born_nonneg ρ, M.born_sum ρ⟩

end FinitePOVM

end
end Paper26.QuantumModel
