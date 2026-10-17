import Paper26.WeightedTraceCS
import Paper26.JordanLossMeasurability

/-!
# Actual matrix comparison inequalities

The SLD for a supported difference is constructed in the actual output
eigenbasis, with inverse zero on the kernel. Its Hermitian equation and
energy are proved, including singular outputs. The measured classical
chi-squared comparison uses the genuine null-denominator convention.
No comparison assertion is an external input.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal MatrixOrder
open MeasureTheory

namespace Paper26.ComparisonInequalities
open QuantumModel ContinuousPOVM WeightedTraceCS TailConvexity Normalization
open SupportCompression JordanLossMeasurability

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]

omit [DecidableEq ι] in
private theorem density_nonempty (ρ : Density ι) : Nonempty ι := by
  by_contra h
  haveI : IsEmpty ι := not_nonempty_iff.mp h
  simpa [Matrix.trace] using ρ.trace_one

omit [Fintype ι] [DecidableEq ι] in
theorem inverseJordan_hermitian (a : ι → ℝ) {X : Matrix ι ι ℂ} (hX : X.IsHermitian) :
    (inverseJordan a X).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [inverseJordan, star_mul, hX.apply i j, add_comm, Complex.star_def,
    Complex.conj_ofReal, mul_comm]

/-- The actual spectral SLD, using the totalized inverse on zero denominators. -/
def supportedSLD (ρ σ : Density ι) : Matrix ι ι ℂ :=
  conjugate (σ.eigenbasis : Matrix ι ι ℂ)
    (inverseJordan σ.spectrum (eigenDifference ρ σ))

theorem supportedSLD_hermitian (ρ σ : Density ι) : (supportedSLD ρ σ).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _
    (inverseJordan_hermitian σ.spectrum (eigenDifference_hermitian ρ σ))

theorem diagonal_supported_equation (ρ σ : Density ι) (h : SupportContained ρ σ) :
    diagonalMatrix σ.spectrum * inverseJordan σ.spectrum (eigenDifference ρ σ) +
      inverseJordan σ.spectrum (eigenDifference ρ σ) * diagonalMatrix σ.spectrum =
        (2 : ℂ) • eigenDifference ρ σ := by
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul, diagonalMatrix,
    Matrix.diagonal_mul, Matrix.mul_diagonal, inverseJordan]
  by_cases hz : σ.spectrum i + σ.spectrum j = 0
  · have hj : σ.spectrum j = 0 := by
      have hi0 := σ.spectrum_nonneg i
      have hj0 := σ.spectrum_nonneg j
      linarith
    rw [eigenDifference_zero_column ρ σ h j hj i]
    simp
  · have hc : (σ.spectrum i : ℂ) + (σ.spectrum j : ℂ) ≠ 0 := by exact_mod_cast hz
    push_cast
    field_simp [hc]

theorem supportedSLD_equation (ρ σ : Density ι) (h : SupportContained ρ σ) :
    σ.matrix * supportedSLD ρ σ + supportedSLD ρ σ * σ.matrix =
      (2 : ℂ) • (ρ.matrix - σ.matrix) := by
  have he := congrArg (conjugate (σ.eigenbasis : Matrix ι ι ℂ))
    (diagonal_supported_equation ρ σ h)
  rw [conjugate_add, conjugate_mul _ _ _ (PositiveLossBridge.unitary_left σ.eigenbasis),
    conjugate_mul _ _ _ (PositiveLossBridge.unitary_left σ.eigenbasis), conjugate_smul] at he
  have hd : conjugate (σ.eigenbasis : Matrix ι ι ℂ) (diagonalMatrix σ.spectrum) = σ.matrix :=
    (PositiveLossBridge.density_spectral_reconstruction σ).symm
  have hΔ : conjugate (σ.eigenbasis : Matrix ι ι ℂ) (eigenDifference ρ σ) = ρ.matrix - σ.matrix :=
    conjugate_coordinates _ _ (PositiveLossBridge.unitary_right σ.eigenbasis)
  rw [hd, hΔ] at he
  exact he

theorem supportedSLD_tangent (ρ σ : Density ι) (h : SupportContained ρ σ) :
    sldTangent σ.matrix (supportedSLD ρ σ) = ρ.matrix - σ.matrix := by
  rw [sldTangent, supportedSLD_equation ρ σ h]
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

section Nonempty
variable [Nonempty ι]

/-- The constructed matrix is exactly the intrinsic Moore--Penrose Jordan
inverse applied to the actual vectorized difference, not a separate model. -/
theorem supportedSLD_vec (ρ σ : Density ι) :
    Matrix.vec (supportedSLD ρ σ) =
      pseudoJordan σ *ᵥ Matrix.vec (ρ.matrix - σ.matrix) := by
  rw [supportedSLD, ← conjugationMatrix_action, pseudoJordan_spectral]
  change conjugationMatrix (σ.eigenbasis : Matrix ι ι ℂ) *ᵥ
      Matrix.vec (inverseJordan σ.spectrum (eigenDifference ρ σ)) =
    (conjugationMatrix (σ.eigenbasis : Matrix ι ι ℂ) *
      diagonalMatrix (fun p => (jordanSpectrum σ.spectrum p)⁻¹) *
        (conjugationMatrix (σ.eigenbasis : Matrix ι ι ℂ))ᴴ) *ᵥ
          Matrix.vec (ρ.matrix - σ.matrix)
  have hcoord : (conjugationMatrix (σ.eigenbasis : Matrix ι ι ℂ))ᴴ *ᵥ
      Matrix.vec (ρ.matrix - σ.matrix) = Matrix.vec (eigenDifference ρ σ) := by
    rw [conjugationMatrix_adjoint, conjugationMatrix_action]
    simp only [conjugate, Matrix.conjTranspose_conjTranspose, eigenDifference,
      Matrix.star_eq_conjTranspose]
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hcoord]
  congr 1
  ext p
  simp only [diagonalMatrix, Matrix.mulVec_diagonal, Matrix.vec, inverseJordan, jordanSpectrum]
  congr 1
  congr 1
  simp only [div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]

theorem supportedSLD_trace (ρ σ : Density ι) :
    pairing (ρ.matrix - σ.matrix) (supportedSLD ρ σ) = buresEnergy ρ σ := by
  have hΔ : ρ.matrix - σ.matrix =
      conjugate (σ.eigenbasis : Matrix ι ι ℂ) (eigenDifference ρ σ) :=
    (conjugate_coordinates _ _ (PositiveLossBridge.unitary_right σ.eigenbasis)).symm
  unfold supportedSLD pairing
  rw [hΔ, ← conjugate_mul _ _ _ (PositiveLossBridge.unitary_left σ.eigenbasis),
    trace_conjugate _ _ (PositiveLossBridge.unitary_left σ.eigenbasis)]
  change (Matrix.trace (eigenDifference ρ σ *
    SpectralLoss.sldInverse σ.spectrum (eigenDifference ρ σ))).re = _
  rw [SpectralLoss.trace_sldInverse (eigenDifference_hermitian ρ σ), Complex.ofReal_re,
    buresEnergy_spectral]

theorem supportedSLD_energy (ρ σ : Density ι) (h : SupportContained ρ σ) :
    pairing σ.matrix (supportedSLD ρ σ * supportedSLD ρ σ) = buresEnergy ρ σ := by
  rw [← supportedSLD_trace ρ σ, ← supportedSLD_tangent ρ σ h]
  exact (sldTangent_pairing _ _ _ σ.hermitian (supportedSLD_hermitian ρ σ)
    (supportedSLD_hermitian ρ σ)).symm

end Nonempty

theorem born_zero_of_supported (M : DominatedPOVM ι Ω) (ρ σ : Density ι)
    (h : SupportContained ρ σ) {y : Ω} (hy : (M.effect y).PosSemidef)
    (hp : M.born σ y = 0) : M.born ρ y = 0 := by
  have hz := derivative_sld_zero_of_born_zero M σ (supportedSLD ρ σ)
    (supportedSLD_hermitian ρ σ) hy hp
  rw [supportedSLD_tangent ρ σ h, derivative_difference, hp, sub_zero] at hz
  exact hz

theorem measuredChiSquared_eq_supportedFisher (M : DominatedPOVM ι Ω) (ρ σ : Density ι)
    (h : SupportContained ρ σ) :
    measuredChiSquared M ρ σ = measuredFisher M σ (ρ.matrix - σ.matrix) := by
  apply lintegral_congr_ae
  filter_upwards [M.positive_ae] with y hy
  by_cases hp : M.born σ y = 0
  · have hz := born_zero_of_supported M ρ σ h hy hp
    simp only [classicalChiSquaredDensity, hp, hz, if_pos, fisherDensity, ENNReal.ofReal_zero]
  · simp [classicalChiSquaredDensity, hp, fisherDensity, derivative_difference]

/-- Full Lemma 1.4 measured comparison, with singular states, arbitrary
measurable outcomes, and the genuine infinite classical denominator branch. -/
theorem measuredChiSquared_le_chiB (M : DominatedPOVM ι Ω) (ρ σ : Density ι) :
    measuredChiSquared M ρ σ ≤ chiB ρ σ := by
  by_cases h : SupportContained ρ σ
  · letI := density_nonempty ρ
    rw [measuredChiSquared_eq_supportedFisher M ρ σ h, chiB_eq_jordan_energy ρ σ h,
      ← supportedSLD_tangent ρ σ h]
    have hc := measuredFisher_sld_le M σ (supportedSLD ρ σ) (supportedSLD_hermitian ρ σ)
    rwa [supportedSLD_energy ρ σ h] at hc
  · rw [chiB_eq_top_of_not_supportContained ρ σ h]
    exact le_top

/-- Bilinear weighted trace Cauchy--Schwarz, proved by the actual
nonnegative Hermitian square `(H-tK)^2`. -/
theorem weighted_bilinear_cs (σ H K : Matrix ι ι ℂ)
    (hσ : σ.PosSemidef) (hH : H.IsHermitian) (hK : K.IsHermitian) :
    pairing σ (K * H) ^ 2 ≤ pairing σ (H * H) * pairing σ (K * K) := by
  have hKK : (K * K).PosSemidef := by
    simpa only [hK.eq] using Matrix.posSemidef_conjTranspose_mul_self K
  apply (scalar_weighted_cs _ _ _ (pairing_nonneg_psd _ _ hσ hKK) ?_).1
  intro t
  let B := H - t • K
  have hB : B.IsHermitian := by
    simp only [B, Matrix.IsHermitian, Matrix.conjTranspose_sub,
      Matrix.conjTranspose_smul, hH.eq, hK.eq, star_trivial]
  have hBB : (B * B).PosSemidef := by
    simpa only [hB.eq] using Matrix.posSemidef_conjTranspose_mul_self B
  have hn := pairing_nonneg_psd σ (B * B) hσ hBB
  dsimp only [B] at hn
  simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.mul_smul,
    pairing_sub_right, pairing_smul_right] at hn
  rw [← triple_real_flip σ K H hσ.isHermitian hK hH] at hn
  nlinarith [hn]

/-- The CFC definition of the diagonal trace norm has the expected scalar
absolute values; no eigenvalue/norm formula is assumed. -/
theorem traceNorm_diagonal (a : ι → ℝ) :
    CommonCenter.traceNorm (diagonalMatrix a) = ∑ i, |a i| := by
  have hs : CFC.sqrt ((diagonalMatrix a)ᴴ * diagonalMatrix a) =
      diagonalMatrix (fun i => |a i|) := by
    apply CFC.sqrt_unique
    · rw [diagonalMatrix_conjTranspose]
      simp only [diagonalMatrix, Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      nlinarith [sq_abs (a i)]
    · exact (Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr (abs_nonneg (a i)))).nonneg
  unfold CommonCenter.traceNorm
  rw [hs]
  simp [diagonalMatrix, Matrix.trace_diagonal, Complex.re_sum]

/-- A Hermitian matrix has an actual Hermitian sign witness. Zero eigenvalues
are assigned sign `+1`, so the witness squares exactly to the identity. -/
theorem traceNorm_sign_witness (D : Matrix ι ι ℂ) (hD : D.IsHermitian) :
    ∃ K : Matrix ι ι ℂ, K.IsHermitian ∧ K * K = 1 ∧
      pairing D K = CommonCenter.traceNorm D := by
  let U := hD.eigenvectorUnitary
  let a := hD.eigenvalues
  let s : ι → ℝ := fun i => if 0 ≤ a i then 1 else -1
  let K := conjugate (U : Matrix ι ι ℂ) (diagonalMatrix s)
  have hs (i : ι) : s i * s i = 1 := by dsimp [s]; split_ifs <;> norm_num
  have hd : diagonalMatrix s * diagonalMatrix s = (1 : Matrix ι ι ℂ) := by
    simp only [diagonalMatrix, Matrix.diagonal_mul_diagonal]
    have he : (fun i => (s i : ℂ) * (s i : ℂ)) = fun _ : ι => (1 : ℂ) := by
      funext i
      rw [← Complex.ofReal_mul, hs, Complex.ofReal_one]
    rw [he, Matrix.diagonal_one]
  have hspec : D = conjugate (U : Matrix ι ι ℂ) (diagonalMatrix a) := by
    simpa only [U, a, conjugate, diagonalMatrix, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hD.spectral_theorem
  refine ⟨K, Matrix.isHermitian_mul_mul_conjTranspose _ (diagonalMatrix_conjTranspose s), ?_, ?_⟩
  · change conjugate (U : Matrix ι ι ℂ) (diagonalMatrix s) *
      conjugate (U : Matrix ι ι ℂ) (diagonalMatrix s) = _
    rw [← conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U), hd]
    simpa only [conjugate, Matrix.mul_one] using PositiveLossBridge.unitary_right U
  · change pairing D (conjugate (U : Matrix ι ι ℂ) (diagonalMatrix s)) = _
    rw [hspec]
    unfold pairing
    rw [← conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
      trace_conjugate _ _ (PositiveLossBridge.unitary_left U), CommonCenter.traceNorm_conjugate,
      traceNorm_diagonal]
    simp only [diagonalMatrix, Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal,
      Complex.re_sum, ← Complex.ofReal_mul, Complex.ofReal_re]
    apply Finset.sum_congr rfl
    intro i _
    dsimp [s]
    split_ifs with hi
    · simp [abs_of_nonneg hi]
    · simp [abs_of_neg (lt_of_not_ge hi)]

/-- Complete Lemma 1.4 trace-norm comparison, on actual finite complex
density matrices, including singular outputs and the infinite loss branch. -/
theorem traceNorm_sq_le_chiB (ρ σ : Density ι) :
    ENNReal.ofReal (CommonCenter.traceNorm (ρ.matrix - σ.matrix) ^ 2) ≤ chiB ρ σ := by
  by_cases h : SupportContained ρ σ
  · letI := density_nonempty ρ
    obtain ⟨K, hK, hKK, hnorm⟩ := traceNorm_sign_witness (ρ.matrix - σ.matrix)
      (ρ.hermitian.sub σ.hermitian)
    have hcs := weighted_bilinear_cs σ.matrix (supportedSLD ρ σ) K σ.positive
      (supportedSLD_hermitian ρ σ) hK
    have hcross : pairing (ρ.matrix - σ.matrix) K =
        pairing σ.matrix (K * supportedSLD ρ σ) := by
      rw [← supportedSLD_tangent ρ σ h]
      exact sldTangent_pairing _ _ _ σ.hermitian hK (supportedSLD_hermitian ρ σ)
    rw [← hcross, hnorm, supportedSLD_energy ρ σ h, hKK] at hcs
    have htr : pairing σ.matrix (1 : Matrix ι ι ℂ) = 1 := by
      simp only [pairing, Matrix.mul_one, σ.trace_one, Complex.one_re]
    rw [htr, mul_one] at hcs
    rw [chiB_eq_jordan_energy ρ σ h]
    exact ENNReal.ofReal_le_ofReal hcs
  · rw [chiB_eq_top_of_not_supportContained ρ σ h]
    exact le_top

/-- The full actual comparison package, combining the two native Lemma 1.4
inequalities with the already proved quantum spectral-loss ordering. -/
theorem lemma_1_4 (M : DominatedPOVM ι Ω) (ρ σ : Density ι) :
    ENNReal.ofReal (CommonCenter.traceNorm (ρ.matrix - σ.matrix) ^ 2) ≤ chiB ρ σ ∧
    measuredChiSquared M ρ σ ≤ chiB ρ σ ∧
    chiB ρ σ ≤ chiG ρ σ ∧ chiG ρ σ ≤ chiR ρ σ :=
  ⟨traceNorm_sq_le_chiB ρ σ, measuredChiSquared_le_chiB M ρ σ, loss_comparison ρ σ⟩

end Paper26.ComparisonInequalities
