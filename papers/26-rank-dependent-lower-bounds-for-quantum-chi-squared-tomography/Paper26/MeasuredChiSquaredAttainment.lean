import Paper26.ComparisonInequalities
import Paper26.AlignedFisherBudget

/-!
# Attainment of measured Bures chi-squared by an actual projective POVM

For a supported pair, measure the spectral projections of its actual
Hermitian SLD.  For an unsupported pair, an output spectral projection on
its kernel has positive input mass and gives infinite classical loss.
All measurements and their Born probabilities are concrete finite matrix
POVMs.  No attainment or comparison theorem is an external input.
-/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.MeasuredChiSquaredAttainment

open QuantumModel ContinuousPOVM Normalization TailConvexity
open WeightedTraceCS ComparisonInequalities SupportCompression

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance discreteOutcome : MeasurableSpace ι := ⊤

def coordinateProjection (i : ι) : Matrix ι ι ℂ := Matrix.diagonal (Pi.single i 1)

def basisEffect (U : Matrix.unitaryGroup ι ℂ) (i : ι) : Matrix ι ι ℂ :=
  conjugate (U : Matrix ι ι ℂ) (coordinateProjection i)

theorem coordinateProjection_posSemidef (i : ι) : (coordinateProjection i).PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro j
  by_cases h : j = i <;> simp [h, Pi.single_apply]

/-- The actual rank-one orthogonal projective measurement in the basis U. -/
def basisPOVM (U : Matrix.unitaryGroup ι ℂ) : FinitePOVM ι ι where
  effect := basisEffect U
  positive i := (coordinateProjection_posSemidef i).mul_mul_conjTranspose_same _
  total := by
    change (∑ i, (U : Matrix ι ι ℂ) * coordinateProjection i * (U : Matrix ι ι ℂ)ᴴ) = 1
    rw [← Matrix.sum_mul, ← Matrix.mul_sum]
    have hd : (∑ i : ι, coordinateProjection i) = (1 : Matrix ι ι ℂ) := by
      ext a b
      by_cases hab : a = b
      · subst b
        simp [coordinateProjection, Matrix.sum_apply, Pi.single_apply]
      · simp [coordinateProjection, Matrix.sum_apply, hab]
    rw [hd, Matrix.mul_one, PositiveLossBridge.unitary_right U]

/-- A finite matrix POVM is represented by counting reference measure. -/
def toDominated (M : FinitePOVM ι ι) : DominatedPOVM ι ι where
  reference := Measure.count
  reference_finite := inferInstance
  effect := M.effect
  entry_measurable _ _ := measurable_of_countable _
  positive_ae := ae_of_all _ M.positive
  entry_integrable _ _ := Integrable.of_finite
  total a b := by
    rw [integral_count]
    simpa only [Matrix.sum_apply] using congrArg (fun A => A a b) M.total

@[simp] theorem toDominated_born (M : FinitePOVM ι ι) (ρ : Density ι) (i : ι) :
    (toDominated M).born ρ i = M.born ρ i := rfl

theorem trace_basisEffect (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) (i : ι) :
    Matrix.trace (A * basisEffect U i) = coordinates (U : Matrix ι ι ℂ) A i i := by
  calc
    _ = Matrix.trace ((A * (U : Matrix ι ι ℂ) * coordinateProjection i) *
        (U : Matrix ι ι ℂ)ᴴ) := by simp only [basisEffect, conjugate, Matrix.mul_assoc]
    _ = Matrix.trace ((U : Matrix ι ι ℂ)ᴴ *
        (A * (U : Matrix ι ι ℂ) * coordinateProjection i)) := Matrix.trace_mul_comm _ _
    _ = Matrix.trace (coordinates (U : Matrix ι ι ℂ) A * coordinateProjection i) := by
      simp only [coordinates, Matrix.mul_assoc]
    _ = _ := by simp [coordinateProjection, Matrix.trace, Matrix.mul_diagonal, Pi.single_apply]

theorem basisPOVM_born (U : Matrix.unitaryGroup ι ℂ) (ρ : Density ι) (i : ι) :
    (basisPOVM U).born ρ i = (coordinates (U : Matrix ι ι ℂ) ρ.matrix i i).re := by
  exact congrArg Complex.re (trace_basisEffect U ρ.matrix i)

/-- The actual measured classical chi-squared is a finite sum with its
genuine infinite branch at a positive input / zero output outcome. -/
theorem measuredChiSquared_toDominated (M : FinitePOVM ι ι) (ρ σ : Density ι) :
    measuredChiSquared (toDominated M) ρ σ =
      ∑ i, classicalChiSquaredDensity (M.born ρ i) (M.born σ i) := by
  simp only [measuredChiSquared, toDominated, lintegral_count, tsum_fintype]
  rfl

theorem spectral_coordinates (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    coordinates (hH.eigenvectorUnitary : Matrix ι ι ℂ) H = diagonalMatrix hH.eigenvalues := by
  simpa only [coordinates, diagonalMatrix, Matrix.star_eq_conjTranspose, Function.comp_def] using
    hH.star_mul_self_mul_eq_diagonal

/-- In the SLD eigenbasis, every actual outcome obeys p-q=lambda*q. -/
theorem supported_born_difference (ρ σ : Density ι) (h : SupportContained ρ σ) (i : ι) :
    let hH := supportedSLD_hermitian ρ σ
    let M := basisPOVM hH.eigenvectorUnitary
    M.born ρ i - M.born σ i = hH.eigenvalues i * M.born σ i := by
  let H := supportedSLD ρ σ
  let hH := supportedSLD_hermitian ρ σ
  let U := hH.eigenvectorUnitary
  have he := congrArg (coordinates (U : Matrix ι ι ℂ)) (supportedSLD_equation ρ σ h)
  rw [coordinates_add, coordinates_mul _ _ _ (PositiveLossBridge.unitary_right U),
    coordinates_mul _ _ _ (PositiveLossBridge.unitary_right U), coordinates_smul,
    coordinates_sub, spectral_coordinates H hH] at he
  have hi := congrArg (fun A : Matrix ι ι ℂ => (A i i).re) he
  simp only [Matrix.add_apply, diagonalMatrix, Matrix.mul_diagonal, Matrix.diagonal_mul,
    Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Complex.sub_re, Complex.add_re,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, sub_zero] at hi
  norm_num at hi
  change (basisPOVM U).born ρ i - (basisPOVM U).born σ i =
    hH.eigenvalues i * (basisPOVM U).born σ i
  rw [basisPOVM_born, basisPOVM_born]
  linarith

theorem trace_mul_conjugate_diagonal (U : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) (a : ι → ℝ) :
    (Matrix.trace (A * conjugate (U : Matrix ι ι ℂ) (diagonalMatrix a))).re =
      ∑ i, a i * (coordinates (U : Matrix ι ι ℂ) A i i).re := by
  have ht : Matrix.trace (A * conjugate (U : Matrix ι ι ℂ) (diagonalMatrix a)) =
      Matrix.trace (coordinates (U : Matrix ι ι ℂ) A * diagonalMatrix a) := by
    calc
      _ = Matrix.trace ((A * (U : Matrix ι ι ℂ) * diagonalMatrix a) *
          (U : Matrix ι ι ℂ)ᴴ) := by simp only [conjugate, Matrix.mul_assoc]
      _ = Matrix.trace ((U : Matrix ι ι ℂ)ᴴ *
          (A * (U : Matrix ι ι ℂ) * diagonalMatrix a)) := Matrix.trace_mul_comm _ _
      _ = _ := by simp only [coordinates, Matrix.mul_assoc]
  rw [ht]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal, diagonalMatrix, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)

theorem spectral_energy (σ : Density ι) (H : Matrix ι ι ℂ) (hH : H.IsHermitian) :
    pairing σ.matrix (H * H) =
      ∑ i, hH.eigenvalues i ^ 2 * (basisPOVM hH.eigenvectorUnitary).born σ i := by
  let U := hH.eigenvectorUnitary
  have hs : H = conjugate (U : Matrix ι ι ℂ) (diagonalMatrix hH.eigenvalues) := by
    simpa only [U, conjugate, diagonalMatrix, Matrix.star_eq_conjTranspose,
      Function.comp_def] using hH.spectral_theorem
  have hh : H * H = conjugate (U : Matrix ι ι ℂ)
      (diagonalMatrix (fun i => hH.eigenvalues i ^ 2)) := by
    calc
      _ = conjugate (U : Matrix ι ι ℂ) (diagonalMatrix hH.eigenvalues) *
          conjugate (U : Matrix ι ι ℂ) (diagonalMatrix hH.eigenvalues) := congrArg₂ (· * ·) hs hs
      _ = _ := by
        rw [← conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U)]
        congr 1
        unfold diagonalMatrix
        rw [Matrix.diagonal_mul_diagonal]
        congr 1
        funext i
        simp only [pow_two, Complex.ofReal_mul]
  rw [hh]
  change (Matrix.trace (σ.matrix * conjugate (U : Matrix ι ι ℂ)
    (diagonalMatrix (fun i => hH.eigenvalues i ^ 2)))).re = _
  rw [trace_mul_conjugate_diagonal]
  simp only [basisPOVM_born]
  rfl

theorem classicalChiSquaredDensity_of_score {p q t : ℝ}
    (hscore : p - q = t * q) :
    classicalChiSquaredDensity p q = ENNReal.ofReal (t ^ 2 * q) := by
  by_cases hz : q = 0
  · have hp : p = 0 := by rw [hz] at hscore; linarith
    simp [classicalChiSquaredDensity, hz, hp]
  · simp only [classicalChiSquaredDensity, if_neg hz, hscore]
    congr 1
    field_simp

/-- On every supported pair, measuring the spectral projections of its
constructed actual SLD attains the full Bures chi-squared loss. -/
theorem supported_attainment [Nonempty ι] (ρ σ : Density ι) (h : SupportContained ρ σ) :
    measuredChiSquared (toDominated (basisPOVM (supportedSLD_hermitian ρ σ).eigenvectorUnitary))
      ρ σ = chiB ρ σ := by
  let hH := supportedSLD_hermitian ρ σ
  let M := basisPOVM hH.eigenvectorUnitary
  rw [measuredChiSquared_toDominated]
  have hd (i : ι) : classicalChiSquaredDensity (M.born ρ i) (M.born σ i) =
      ENNReal.ofReal (hH.eigenvalues i ^ 2 * M.born σ i) :=
    classicalChiSquaredDensity_of_score (supported_born_difference ρ σ h i)
  change (∑ i, classicalChiSquaredDensity (M.born ρ i) (M.born σ i)) = _
  simp_rw [hd]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (M.born_nonneg σ i)),
    ← spectral_energy σ (supportedSLD ρ σ) hH, supportedSLD_energy ρ σ h,
    JordanLossMeasurability.chiB_eq_jordan_energy ρ σ h]

theorem basisPOVM_born_eigenbasis (σ : Density ι) (i : ι) :
    (basisPOVM σ.eigenbasis).born σ i = σ.spectrum i := by
  rw [basisPOVM_born, density_coordinates_diagonal]
  simp only [diagonalMatrix, Matrix.diagonal_apply_eq, Complex.ofReal_re]

theorem psd_column_zero_of_diagonal_zero (A : Matrix ι ι ℂ) (hA : A.PosSemidef)
    (j : ι) (hj : (A j j).re = 0) (i : ι) : A i j = 0 := by
  apply Complex.normSq_eq_zero.mp
  apply le_antisymm _ (Complex.normSq_nonneg _)
  have hc := AlignedFisherBudget.psd_entry_normSq_le A hA i j
  simpa only [hj, mul_zero] using hc

/-- Vanishing input probabilities on every zero-output spectral coordinate
forces actual support inclusion, using PSD to eliminate the entire columns. -/
theorem support_of_zero_spectral_born (ρ σ : Density ι)
    (hz : ∀ j, σ.spectrum j = 0 → (basisPOVM σ.eigenbasis).born ρ j = 0) :
    SupportContained ρ σ := by
  let U := σ.eigenbasis
  let C := coordinates (U : Matrix ι ι ℂ) ρ.matrix
  have hC : C.PosSemidef := ρ.positive.conjTranspose_mul_mul_same (U : Matrix ι ι ℂ)
  have hc : KernelContained C (diagonalMatrix σ.spectrum) := by
    intro v hv
    ext i
    change ∑ j, C i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : σ.spectrum j = 0
    · have hdiag : (C j j).re = 0 := by
        simpa only [basisPOVM_born] using hz j hj
      rw [psd_column_zero_of_diagonal_zero C hC j hdiag i, zero_mul]
    · have hvj := congrFun hv j
      simp only [diagonalMatrix, Matrix.mulVec_diagonal, Pi.zero_apply] at hvj
      have hsj : (σ.spectrum j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hv0 : v j = 0 := (mul_eq_zero.mp hvj).resolve_left hsj
      rw [hv0, mul_zero]
  have hb := kernelContained_conjugate U hc
  have hρ : conjugate (U : Matrix ι ι ℂ) C = ρ.matrix :=
    conjugate_coordinates _ _ (PositiveLossBridge.unitary_right U)
  have hσ : conjugate (U : Matrix ι ι ℂ) (diagonalMatrix σ.spectrum) = σ.matrix :=
    (PositiveLossBridge.density_spectral_reconstruction σ).symm
  rw [hρ, hσ] at hb
  exact hb

/-- If support fails, the actual output spectral measurement detects an
outcome of zero output probability and positive input probability. -/
theorem exists_zero_output_positive_input (ρ σ : Density ι) (h : ¬ SupportContained ρ σ) :
    ∃ i, (basisPOVM σ.eigenbasis).born σ i = 0 ∧
      0 < (basisPOVM σ.eigenbasis).born ρ i := by
  by_contra hn
  push_neg at hn
  apply h
  apply support_of_zero_spectral_born
  intro j hj
  have hq : (basisPOVM σ.eigenbasis).born σ j = 0 := by
    rw [basisPOVM_born_eigenbasis, hj]
  exact le_antisymm (hn j hq) ((basisPOVM σ.eigenbasis).born_nonneg ρ j)

/-- The infinite singular-support branch is attained by an actual finite
projective measurement, with the true infinite classical denominator convention. -/
theorem unsupported_attainment (ρ σ : Density ι) (h : ¬ SupportContained ρ σ) :
    measuredChiSquared (toDominated (basisPOVM σ.eigenbasis)) ρ σ = chiB ρ σ := by
  rw [chiB_eq_top_of_not_supportContained ρ σ h, measuredChiSquared_toDominated]
  obtain ⟨i, hq, hp⟩ := exists_zero_output_positive_input ρ σ h
  have ht : classicalChiSquaredDensity ((basisPOVM σ.eigenbasis).born ρ i)
      ((basisPOVM σ.eigenbasis).born σ i) = ∞ := by
    simp only [classicalChiSquaredDensity, hq, if_pos, if_neg hp.ne']
  apply top_unique
  calc
    _ = classicalChiSquaredDensity ((basisPOVM σ.eigenbasis).born ρ i)
        ((basisPOVM σ.eigenbasis).born σ i) := ht.symm
    _ ≤ _ := Finset.single_le_sum
      (f := fun j : ι => classicalChiSquaredDensity ((basisPOVM σ.eigenbasis).born ρ j)
        ((basisPOVM σ.eigenbasis).born σ j))
      (fun _ _ => bot_le) (Finset.mem_univ i)

/-- One concrete attaining projective POVM, chosen for each pair of states. -/
def attainingPOVM (ρ σ : Density ι) : FinitePOVM ι ι := by
  classical
  exact if SupportContained ρ σ then
    basisPOVM (supportedSLD_hermitian ρ σ).eigenvectorUnitary else basisPOVM σ.eigenbasis

/-- Exact attainment for all actual states, including singular and infinite loss. -/
theorem attainingPOVM_eq (ρ σ : Density ι) :
    measuredChiSquared (toDominated (attainingPOVM ρ σ)) ρ σ = chiB ρ σ := by
  classical
  letI : Nonempty ι := by
    by_contra hn
    letI : IsEmpty ι := not_nonempty_iff.mp hn
    simpa [Matrix.trace] using ρ.trace_one
  by_cases h : SupportContained ρ σ
  · simpa only [attainingPOVM, if_pos h] using supported_attainment ρ σ h
  · simpa only [attainingPOVM, if_neg h] using unsupported_attainment ρ σ h

theorem exists_attaining_finitePOVM (ρ σ : Density ι) :
    ∃ M : FinitePOVM ι ι, measuredChiSquared (toDominated M) ρ σ = chiB ρ σ :=
  ⟨attainingPOVM ρ σ, attainingPOVM_eq ρ σ⟩

/-- Lemma 1.4's maximum has an actual finite-outcome measurement witness. -/
theorem exists_attaining_measurement (ρ σ : Density ι) :
    ∃ M : DominatedPOVM ι ι, measuredChiSquared M ρ σ = chiB ρ σ :=
  ⟨toDominated (attainingPOVM ρ σ), attainingPOVM_eq ρ σ⟩

/-- The same fixed attaining measurement dominates every actual dominated
POVM on every arbitrary measurable outcome space. -/
theorem attaining_dominates {Ω : Type*} [MeasurableSpace Ω]
    (N : DominatedPOVM ι Ω) (ρ σ : Density ι) :
    measuredChiSquared N ρ σ ≤ measuredChiSquared (toDominated (attainingPOVM ρ σ)) ρ σ := by
  rw [attainingPOVM_eq]
  exact ComparisonInequalities.measuredChiSquared_le_chiB N ρ σ

end Paper26.MeasuredChiSquaredAttainment
