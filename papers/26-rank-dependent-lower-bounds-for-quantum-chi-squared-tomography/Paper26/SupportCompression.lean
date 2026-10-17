import Paper26.CommonCenter

/-!
# Singular-output support and Moore–Penrose trace formulas

The inverse below is defined from the quantum model's actual chosen spectral
basis. Algebraic uniqueness removes every dependence on that choice. No loss
invariance or common-center conclusion is assumed.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal MatrixOrder

namespace Paper26.SupportCompression
open QuantumModel

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A Hermitian commuting reflexive generalized inverse. -/
structure HermitianInverse (A B : Matrix ι ι ℂ) : Prop where
  hermitian : B.IsHermitian
  commute : A * B = B * A
  outer : A * B * A = A
  inner : B * A * B = B

omit [DecidableEq ι] in
/-- Algebraic Moore–Penrose uniqueness, proved without spectral-basis choices. -/
theorem HermitianInverse.unique {A B C : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : HermitianInverse A B) (hC : HermitianInverse A C) : B = C := by
  have hE : (A * B)ᴴ = A * B := by
    rw [Matrix.conjTranspose_mul, hB.hermitian.eq, hA.eq]
    exact hB.commute.symm
  have hF : (A * C)ᴴ = A * C := by
    rw [Matrix.conjTranspose_mul, hC.hermitian.eq, hA.eq]
    exact hC.commute.symm
  have hEF : (A * B) * (A * C) = A * C := by
    rw [← Matrix.mul_assoc, hB.outer]
  have hFE : (A * C) * (A * B) = A * B := by
    rw [← Matrix.mul_assoc, hC.outer]
  have ht := congrArg Matrix.conjTranspose hEF
  rw [Matrix.conjTranspose_mul, hE, hF] at ht
  have hp : A * B = A * C := hFE.symm.trans ht
  have hl : B * A = C * A := hB.commute.symm.trans (hp.trans hC.commute)
  calc
    B = B * A * B := hB.inner.symm
    _ = B * (A * B) := Matrix.mul_assoc _ _ _
    _ = B * (A * C) := by rw [hp]
    _ = B * A * C := (Matrix.mul_assoc _ _ _).symm
    _ = C * A * C := by rw [hl]
    _ = C := hC.inner

lemma diagonal_hermitian (a : ι → ℝ) : (Normalization.diagonalMatrix a).IsHermitian := by
  exact Normalization.diagonalMatrix_conjTranspose a

lemma diagonal_inverse_properties (a : ι → ℝ) :
    HermitianInverse (Normalization.diagonalMatrix a)
      (Normalization.diagonalMatrix (fun i => (a i)⁻¹)) := by
  refine ⟨diagonal_hermitian _, ?_, ?_, ?_⟩
  · unfold Normalization.diagonalMatrix
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  · unfold Normalization.diagonalMatrix
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hz : a i = 0
    · simp [hz]
    · push_cast
      simp [hz]
  · unfold Normalization.diagonalMatrix
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    by_cases hz : a i = 0
    · simp [hz]
    · push_cast
      simp [hz]

lemma HermitianInverse.conjugate {A B : Matrix ι ι ℂ} (h : HermitianInverse A B)
    (U : Matrix.unitaryGroup ι ℂ) :
    HermitianInverse (Normalization.conjugate (U : Matrix ι ι ℂ) A)
      (Normalization.conjugate (U : Matrix ι ι ℂ) B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [Normalization.conjugate] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℂ) h.hermitian
  · rw [← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
      ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U), h.commute]
  · rw [← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
      ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U), h.outer]
  · rw [← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
      ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U), h.inner]

/-- Spectral Moore–Penrose inverse of the actual output density; `0⁻¹ = 0`. -/
def pinv (σ : Density ι) : Matrix ι ι ℂ :=
  Normalization.conjugate (σ.eigenbasis : Matrix ι ι ℂ)
    (Normalization.diagonalMatrix (fun i => (σ.spectrum i)⁻¹))

theorem pinv_properties (σ : Density ι) : HermitianInverse σ.matrix (pinv σ) := by
  rw [PositiveLossBridge.density_spectral_reconstruction σ]
  exact (diagonal_inverse_properties σ.spectrum).conjugate σ.eigenbasis

theorem pinv_posSemidef (σ : Density ι) : (pinv σ).PosSemidef := by
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  exact Matrix.PosSemidef.diagonal (fun i => RCLike.ofReal_nonneg.mpr
    (inv_nonneg.mpr (σ.spectrum_nonneg i)))

/-- Actual generalized inverses are equivariant under every unitary, including
singular outputs, by the proved algebraic uniqueness theorem. -/
theorem pinv_conjugate (U : Matrix.unitaryGroup ι ℂ) (σ : Density ι) :
    pinv (PositiveLossBridge.conjugateDensity U σ) =
      Normalization.conjugate (U : Matrix ι ι ℂ) (pinv σ) := by
  exact (pinv_properties (PositiveLossBridge.conjugateDensity U σ)).unique
    (PositiveLossBridge.conjugateDensity U σ).hermitian
    ((pinv_properties σ).conjugate U)

/-- Reverse kernel inclusion, for arbitrary actual matrices. -/
def KernelContained (R A : Matrix ι ι ℂ) : Prop :=
  ∀ v : ι → ℂ, A *ᵥ v = 0 → R *ᵥ v = 0

lemma kernelContained_conjugate (U : Matrix.unitaryGroup ι ℂ) {R A : Matrix ι ι ℂ}
    (h : KernelContained R A) :
    KernelContained (Normalization.conjugate (U : Matrix ι ι ℂ) R)
      (Normalization.conjugate (U : Matrix ι ι ℂ) A) := by
  intro v hv
  have hv' := hv
  rw [Normalization.conjugate, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv'
  have hz : A *ᵥ ((U : Matrix ι ι ℂ)ᴴ *ᵥ v) = 0 := by
    have ht := congrArg (fun w => (U : Matrix ι ι ℂ)ᴴ *ᵥ w) hv'
    change (U : Matrix ι ι ℂ)ᴴ *ᵥ ((U : Matrix ι ι ℂ) *ᵥ
      (A *ᵥ ((U : Matrix ι ι ℂ)ᴴ *ᵥ v))) = (U : Matrix ι ι ℂ)ᴴ *ᵥ 0 at ht
    rwa [Matrix.mulVec_mulVec (A *ᵥ ((U : Matrix ι ι ℂ)ᴴ *ᵥ v))
      (U : Matrix ι ι ℂ)ᴴ (U : Matrix ι ι ℂ),
      PositiveLossBridge.unitary_left U, Matrix.one_mulVec, Matrix.mulVec_zero] at ht
  have hr := h _ hz
  rw [Normalization.conjugate, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    hr, Matrix.mulVec_zero]


lemma conjugate_star_cancel (U : Matrix.unitaryGroup ι ℂ) (X : Matrix ι ι ℂ) :
    Normalization.conjugate ((star U : Matrix.unitaryGroup ι ℂ) : Matrix ι ι ℂ)
      (Normalization.conjugate (U : Matrix ι ι ℂ) X) = X := by
  simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose,
    Normalization.coordinates, Normalization.conjugate, Matrix.conjTranspose_conjTranspose] using
    Normalization.coordinates_conjugate (U : Matrix ι ι ℂ) X
      (PositiveLossBridge.unitary_left U)

/-- The actual support convention is invariant under simultaneous unitary
conjugation, with no positive-definiteness restriction. -/
theorem supportContained_unitary (U : Matrix.unitaryGroup ι ℂ) (ρ σ : Density ι) :
    SupportContained (PositiveLossBridge.conjugateDensity U ρ)
      (PositiveLossBridge.conjugateDensity U σ) ↔ SupportContained ρ σ := by
  change KernelContained (Normalization.conjugate (U : Matrix ι ι ℂ) ρ.matrix)
    (Normalization.conjugate (U : Matrix ι ι ℂ) σ.matrix) ↔ KernelContained ρ.matrix σ.matrix
  constructor
  · intro h
    have hh := kernelContained_conjugate (star U) h
    rwa [conjugate_star_cancel, conjugate_star_cancel] at hh
  · exact kernelContained_conjugate U


lemma coordinates_kernelContained (U : Matrix.unitaryGroup ι ℂ)
    {R A : Matrix ι ι ℂ} (h : KernelContained R A) :
    KernelContained (Normalization.coordinates (U : Matrix ι ι ℂ) R)
      (Normalization.coordinates (U : Matrix ι ι ℂ) A) := by
  simpa only [unitary.coe_star, Matrix.star_eq_conjTranspose,
    Normalization.conjugate, Normalization.coordinates,
    Matrix.conjTranspose_conjTranspose] using kernelContained_conjugate (star U) h

lemma density_coordinates_diagonal (σ : Density ι) :
    Normalization.coordinates (σ.eigenbasis : Matrix ι ι ℂ) σ.matrix =
      Normalization.diagonalMatrix σ.spectrum := by
  simpa only [Normalization.coordinates, Normalization.diagonalMatrix,
    Matrix.star_eq_conjTranspose] using σ.diagonal_in_eigenbasis

/-- Support inclusion forces every zero-eigenvalue column of the actual
transformed error to vanish. -/
theorem eigenDifference_zero_column (ρ σ : Density ι) (h : SupportContained ρ σ)
    (j : ι) (hj : σ.spectrum j = 0) (i : ι) : eigenDifference ρ σ i j = 0 := by
  have hc := coordinates_kernelContained σ.eigenbasis h
  rw [density_coordinates_diagonal] at hc
  have hz : Normalization.diagonalMatrix σ.spectrum *ᵥ Pi.single j 1 = 0 := by
    rw [Normalization.diagonalMatrix, Matrix.diagonal_mulVec_single, hj]
    simp
  have hr := congrFun (hc (Pi.single j 1) hz) i
  have hr' : Normalization.coordinates (σ.eigenbasis : Matrix ι ι ℂ) ρ.matrix i j = 0 := by
    simpa only [Matrix.mulVec_single_one, Matrix.col_apply, Pi.zero_apply] using hr
  rw [PositiveLossBridge.eigenDifference_eq_coordinates, Matrix.sub_apply, hr']
  have hd : Normalization.diagonalMatrix σ.spectrum i j = 0 := by
    by_cases hij : i = j
    · subst i
      simp [Normalization.diagonalMatrix, hj]
    · simp [Normalization.diagonalMatrix, hij]
  simp [hd]

theorem eigenDifference_zero_row (ρ σ : Density ι) (h : SupportContained ρ σ)
    (i : ι) (hi : σ.spectrum i = 0) (j : ι) : eigenDifference ρ σ i j = 0 := by
  have he := congrArg (fun X : Matrix ι ι ℂ => X i j) (eigenDifference_hermitian ρ σ).eq
  simpa only [Matrix.conjTranspose_apply, eigenDifference_zero_column ρ σ h i hi j,
    star_zero] using he.symm

lemma sum_support_eq (σ : Density ι) (f : ι → ℝ)
    (hz : ∀ i, ¬ 0 < σ.spectrum i → f i = 0) :
    (∑ i : SupportIndex σ, f i.val) = ∑ i, f i := by
  classical
  have ht := Fintype.sum_subtype_add_sum_subtype (fun i => 0 < σ.spectrum i) f
  have hc : (∑ i : {i // ¬ 0 < σ.spectrum i}, f i.val) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    exact hz i.val i.property
  rw [hc, add_zero] at ht
  exact ht

/-- The finite-support sum equals the full spectral sum under the actual
support condition; omitted rows vanish, and zero denominator columns use
Lean's exact `0⁻¹ = 0` convention. -/
theorem rightInverse_support_eq (ρ σ : Density ι) (h : SupportContained ρ σ) :
    SpectralLoss.rightInverse (supportSpectrum σ) (supportDifference ρ σ) =
      SpectralLoss.rightInverse σ.spectrum (eigenDifference ρ σ) := by
  unfold SpectralLoss.rightInverse supportSpectrum supportDifference
  simp only [Matrix.submatrix_apply]
  calc
    _ = ∑ i, ∑ j : SupportIndex σ,
        Complex.normSq (eigenDifference ρ σ i j.val) / σ.spectrum j.val := by
      apply sum_support_eq σ (fun i => ∑ j : SupportIndex σ,
        Complex.normSq (eigenDifference ρ σ i j.val) / σ.spectrum j.val)
      intro i hi
      have hz : σ.spectrum i = 0 := le_antisymm (le_of_not_gt hi) (σ.spectrum_nonneg i)
      apply Finset.sum_eq_zero
      intro j _
      simp [eigenDifference_zero_row ρ σ h i hz j.val]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply sum_support_eq σ (fun j =>
        Complex.normSq (eigenDifference ρ σ i j) / σ.spectrum j)
      intro j hj
      have hz : σ.spectrum j = 0 := le_antisymm (le_of_not_gt hj) (σ.spectrum_nonneg j)
      simp [hz]

theorem chiR_eq_full_spectral (ρ σ : Density ι) (h : SupportContained ρ σ) :
    chiR ρ σ = ENNReal.ofReal
      (SpectralLoss.rightInverse σ.spectrum (eigenDifference ρ σ)) := by
  rw [chiR, if_pos h, rightInverse_support_eq ρ σ h]

/-- Intrinsic finite trace loss using the proved Moore–Penrose inverse. This
real expression is used only when the actual support condition holds. -/
def rightEnergy (ρ σ : Density ι) : ℝ :=
  (Matrix.trace ((ρ.matrix - σ.matrix) * (ρ.matrix - σ.matrix) * pinv σ)).re

theorem rightEnergy_eq_spectral (ρ σ : Density ι) :
    rightEnergy ρ σ = SpectralLoss.rightInverse σ.spectrum (eigenDifference ρ σ) := by
  have he : ρ.matrix - σ.matrix =
      Normalization.conjugate (σ.eigenbasis : Matrix ι ι ℂ) (eigenDifference ρ σ) := by
    simpa only [eigenDifference, Matrix.star_eq_conjTranspose,
      Normalization.coordinates] using
      (Normalization.conjugate_coordinates (σ.eigenbasis : Matrix ι ι ℂ)
        (ρ.matrix - σ.matrix) (PositiveLossBridge.unitary_right σ.eigenbasis)).symm
  unfold rightEnergy pinv
  rw [he, ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left σ.eigenbasis),
    ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left σ.eigenbasis),
    Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left σ.eigenbasis)]
  have hh := Normalization.rightEnergy_eq_trace
    (Normalization.coordinates (σ.eigenbasis : Matrix ι ι ℂ) ρ.matrix) σ.spectrum
    (Normalization.coordinates_hermitian _ _ ρ.hermitian.eq)
  rw [PositiveLossBridge.rightEnergy_eq_spectral] at hh
  rw [← PositiveLossBridge.eigenDifference_eq_coordinates ρ σ] at hh
  simpa only [one_div] using hh.symm

/-- Full finite χR trace bridge, allowing singular output matrices. -/
theorem chiR_eq_pinv_trace (ρ σ : Density ι) (h : SupportContained ρ σ) :
    chiR ρ σ = ENNReal.ofReal (rightEnergy ρ σ) := by
  rw [chiR_eq_full_spectral ρ σ h, rightEnergy_eq_spectral]

theorem rightEnergy_nonneg (ρ σ : Density ι) : 0 ≤ rightEnergy ρ σ := by
  rw [rightEnergy_eq_spectral]
  unfold SpectralLoss.rightInverse
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact div_nonneg (Complex.normSq_nonneg _) (σ.spectrum_nonneg j)

theorem chiR_toReal_pinv_trace (ρ σ : Density ι) (h : SupportContained ρ σ) :
    (chiR ρ σ).toReal = rightEnergy ρ σ := by
  rw [chiR_eq_pinv_trace ρ σ h, ENNReal.toReal_ofReal (rightEnergy_nonneg ρ σ)]

theorem rightEnergy_conjugate (U : Matrix.unitaryGroup ι ℂ) (ρ σ : Density ι) :
    rightEnergy (PositiveLossBridge.conjugateDensity U ρ)
      (PositiveLossBridge.conjugateDensity U σ) = rightEnergy ρ σ := by
  unfold rightEnergy
  simp only [PositiveLossBridge.conjugateDensity_matrix]
  rw [pinv_conjugate, ← Normalization.conjugate_sub,
    ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
    ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
    Normalization.trace_conjugate _ _ (PositiveLossBridge.unitary_left U)]

/-- Simultaneous unitary invariance of the actual χR for every pair of states,
including singular outputs and infinite unsupported losses. -/
theorem chiR_unitary (U : Matrix.unitaryGroup ι ℂ) (ρ σ : Density ι) :
    chiR (PositiveLossBridge.conjugateDensity U ρ)
      (PositiveLossBridge.conjugateDensity U σ) = chiR ρ σ := by
  by_cases h : SupportContained ρ σ
  · rw [chiR_eq_pinv_trace _ _ ((supportContained_unitary U ρ σ).mpr h),
      chiR_eq_pinv_trace ρ σ h, rightEnergy_conjugate]
  · have hc := mt (supportContained_unitary U ρ σ).mp h
    rw [chiR_eq_top_of_not_supportContained _ _ hc,
      chiR_eq_top_of_not_supportContained _ _ h]


lemma KernelContained.mul_zero {R A X : Matrix ι ι ℂ} (h : KernelContained R A)
    (hAX : A * X = 0) : R * X = 0 := by
  apply Matrix.ext_of_mulVec_single
  intro j
  have hz : A *ᵥ (X *ᵥ Pi.single j 1) = 0 := by
    rw [Matrix.mulVec_mulVec, hAX, Matrix.zero_mulVec]
  have hr := h _ hz
  simpa only [Matrix.mulVec_mulVec, Matrix.zero_mulVec] using hr

/-- Reverse kernel inclusion means that the support projection `σ⁺σ` acts
as the identity on the right of the actual supported matrix. -/
theorem KernelContained.right_projection {R : Matrix ι ι ℂ} (σ : Density ι)
    (h : KernelContained R σ.matrix) : R * pinv σ * σ.matrix = R := by
  have hz : σ.matrix * (1 - pinv σ * σ.matrix) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, (pinv_properties σ).outer,
      sub_self]
  have hr := h.mul_zero hz
  rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc] at hr
  exact (sub_eq_zero.mp hr).symm


/-- A basis-independent exact support test, useful also for measurable events. -/
theorem kernelContained_iff_projection (R : Matrix ι ι ℂ) (σ : Density ι) :
    KernelContained R σ.matrix ↔ R * (1 - pinv σ * σ.matrix) = 0 := by
  constructor
  · intro h
    have hr := h.right_projection σ
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hr, sub_self]
  · intro h v hv
    have he : (1 - pinv σ * σ.matrix) *ᵥ v = v := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv,
        Matrix.mulVec_zero, sub_zero]
    have hz := congrArg (fun X : Matrix ι ι ℂ => X *ᵥ v) h
    change (R * (1 - pinv σ * σ.matrix)) *ᵥ v = (0 : Matrix ι ι ℂ) *ᵥ v at hz
    rwa [← Matrix.mulVec_mulVec, he, Matrix.zero_mulVec] at hz

def pinvRisk (M : Matrix ι ι ℂ) (σ : Density ι) : ℝ :=
  (Matrix.trace (M * pinv σ)).re

lemma pinvRisk_add (M N : Matrix ι ι ℂ) (σ : Density ι) :
    pinvRisk (M + N) σ = pinvRisk M σ + pinvRisk N σ := by
  simp [pinvRisk, Matrix.add_mul, Matrix.trace_add]

lemma pinvRisk_real_smul (b : ℝ) (M : Matrix ι ι ℂ) (σ : Density ι) :
    pinvRisk (b • M) σ = b * pinvRisk M σ := by
  simp [pinvRisk, Matrix.trace_smul, Complex.real_smul, Complex.mul_re]

lemma pinvRisk_square_nonneg (X : Matrix ι ι ℂ) (σ : Density ι) (hX : X.IsHermitian) :
    0 ≤ pinvRisk (X * X) σ := by
  have hp := (pinv_posSemidef σ).mul_mul_conjTranspose_same X
  rw [hX.eq] at hp
  have hn := hp.trace_nonneg
  rw [Matrix.trace_mul_cycle] at hn
  exact hn.1

/-- Completing the weighted square remains valid for singular outputs when
its actual support condition is satisfied. -/
lemma pinvRisk_square_expansion (S : Matrix ι ι ℂ) (σ : Density ι)
    (hS : KernelContained S σ.matrix) (t : ℝ) :
    pinvRisk ((S - (t : ℂ) • σ.matrix) * (S - (t : ℂ) • σ.matrix)) σ =
      pinvRisk (S * S) σ - 2 * t * (Matrix.trace S).re + t ^ 2 := by
  have hs := hS.right_projection σ
  have hc1 : Matrix.trace (S * σ.matrix * pinv σ) = Matrix.trace S := by
    have he : S * σ.matrix * pinv σ = S * pinv σ * σ.matrix := by
      rw [Matrix.mul_assoc, (pinv_properties σ).commute, ← Matrix.mul_assoc]
    rw [he, hs]
  have hc2 : Matrix.trace (σ.matrix * S * pinv σ) = Matrix.trace S := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm, hs]
  have hc3 : Matrix.trace (σ.matrix * σ.matrix * pinv σ) = 1 := by
    rw [Matrix.trace_mul_cycle, ← (pinv_properties σ).commute,
      (pinv_properties σ).outer, σ.trace_one]
  have he : (S - (t : ℂ) • σ.matrix) * (S - (t : ℂ) • σ.matrix) * pinv σ =
      S * S * pinv σ - (S * ((t : ℂ) • σ.matrix)) * pinv σ -
        (((t : ℂ) • σ.matrix) * S) * pinv σ +
          (((t : ℂ) • σ.matrix) * ((t : ℂ) • σ.matrix)) * pinv σ := by
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  unfold pinvRisk
  rw [he]
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.trace_add,
    Matrix.trace_sub, Matrix.trace_smul, hc1, hc2, hc3, smul_eq_mul,
    Complex.add_re, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.one_re, Complex.one_im,
    mul_zero, zero_mul, sub_zero]
  ring

/-- Matrix Cauchy lower bound for every supported density output, including
singular ones, proved by the actual Moore–Penrose weighted square. -/
theorem pinvRisk_lower (S : Matrix ι ι ℂ) (σ : Density ι) (hHerm : S.IsHermitian)
    (hS : KernelContained S σ.matrix) :
    (Matrix.trace S).re ^ 2 ≤ pinvRisk (S * S) σ := by
  let t := (Matrix.trace S).re
  have hX : (S - (t : ℂ) • σ.matrix).IsHermitian := by
    change (S - (t : ℂ) • σ.matrix)ᴴ = S - (t : ℂ) • σ.matrix
    simp [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hHerm.eq, σ.hermitian.eq]
  have hn := pinvRisk_square_nonneg (S - (t : ℂ) • σ.matrix) σ hX
  rw [pinvRisk_square_expansion S σ hS t] at hn
  dsimp [t] at hn
  nlinarith

lemma rightEnergy_expansion (ρ σ : Density ι) (h : SupportContained ρ σ) :
    rightEnergy ρ σ = pinvRisk (ρ.matrix * ρ.matrix) σ - 1 := by
  have he := pinvRisk_square_expansion ρ.matrix σ h 1
  simp only [pinvRisk, Complex.ofReal_one, one_smul,
    one_pow, ρ.trace_one, Complex.one_re] at he
  unfold rightEnergy pinvRisk
  linarith [he]

lemma flat_rightEnergy (P : OrthogonalProjector ι) (hr : 0 < P.matrix.rank)
    (σ : Density ι) (h : SupportContained (P.flat hr) σ) :
    rightEnergy (P.flat hr) σ =
      (((P.matrix.rank : ℝ)⁻¹) ^ 2) * pinvRisk P.matrix σ - 1 := by
  rw [rightEnergy_expansion _ _ h, CommonCenter.flat_square, pinvRisk_real_smul]

omit [DecidableEq ι] in
/-- The square root of a supported projector sum is itself supported. -/
lemma squareRoot_kernelContained (P Q : OrthogonalProjector ι)
    (S : Matrix ι ι ℂ) (hHerm : S.IsHermitian) (hSquare : S * S = P.matrix + Q.matrix)
    (σ : Density ι) (hP : KernelContained P.matrix σ.matrix)
    (hQ : KernelContained Q.matrix σ.matrix) : KernelContained S σ.matrix := by
  intro v hv
  have hp := hP v hv
  have hq := hQ v hv
  apply (Matrix.conjTranspose_mul_self_mulVec_eq_zero S v).mp
  rw [hHerm.eq, hSquare, Matrix.add_mulVec, hp, hq, add_zero]

/-- The core lower bound underlying Proposition B.1 now treats singular
supported outputs as well as positive ones. No principal-angle formula is
assumed in this matrix theorem. -/
theorem flat_pair_average_lower (P Q : OrthogonalProjector ι)
    (hrP : 0 < P.matrix.rank) (hrQ : 0 < Q.matrix.rank)
    (hrank : P.matrix.rank = Q.matrix.rank)
    (S : Matrix ι ι ℂ) (hHerm : S.IsHermitian) (hSquare : S * S = P.matrix + Q.matrix)
    (σ : Density ι) (hP : SupportContained (P.flat hrP) σ)
    (hQ : SupportContained (Q.flat hrQ) σ) :
    (((P.matrix.rank : ℝ)⁻¹) ^ 2) / 2 * (Matrix.trace S).re ^ 2 - 1 ≤
      (rightEnergy (P.flat hrP) σ + rightEnergy (Q.flat hrQ) σ) / 2 := by
  have hPK : KernelContained P.matrix σ.matrix := fun v hv =>
    (CommonCenter.flat_kernel P hrP v).mp (hP v hv)
  have hQK : KernelContained Q.matrix σ.matrix := fun v hv =>
    (CommonCenter.flat_kernel Q hrQ v).mp (hQ v hv)
  have hl := pinvRisk_lower S σ hHerm
    (squareRoot_kernelContained P Q S hHerm hSquare σ hPK hQK)
  rw [hSquare, pinvRisk_add] at hl
  rw [flat_rightEnergy P hrP σ hP, flat_rightEnergy Q hrQ σ hQ, ← hrank]
  have hc : 0 ≤ (((P.matrix.rank : ℝ)⁻¹) ^ 2) := sq_nonneg _
  nlinarith




def traceRadius (P : OrthogonalProjector ι) (S : Matrix ι ι ℂ) : ℝ :=
  (((P.matrix.rank : ℝ)⁻¹) ^ 2) / 2 * (Matrix.trace S).re ^ 2 - 1

/-- The trace-square minimax lower bound over every actual output density. -/
theorem flat_pair_max_lower (P Q : OrthogonalProjector ι)
    (hrP : 0 < P.matrix.rank) (hrQ : 0 < Q.matrix.rank)
    (hrank : P.matrix.rank = Q.matrix.rank)
    (S : Matrix ι ι ℂ) (hHerm : S.IsHermitian) (hSquare : S * S = P.matrix + Q.matrix)
    (σ : Density ι) : ENNReal.ofReal (traceRadius P S) ≤
      max (chiR (P.flat hrP) σ) (chiR (Q.flat hrQ) σ) := by
  by_cases hp : SupportContained (P.flat hrP) σ
  · by_cases hq : SupportContained (Q.flat hrQ) σ
    · have ha := flat_pair_average_lower P Q hrP hrQ hrank S hHerm hSquare σ hp hq
      change traceRadius P S ≤ _ at ha
      rw [chiR_eq_pinv_trace _ _ hp, chiR_eq_pinv_trace _ _ hq]
      by_cases he : rightEnergy (P.flat hrP) σ ≤ rightEnergy (Q.flat hrQ) σ
      · rw [max_eq_right (ENNReal.ofReal_le_ofReal he)]
        apply ENNReal.ofReal_le_ofReal
        linarith
      · rw [max_eq_left (ENNReal.ofReal_le_ofReal (le_of_not_ge he))]
        apply ENNReal.ofReal_le_ofReal
        linarith
    · rw [chiR_eq_top_of_not_supportContained _ _ hq]
      simp
  · rw [chiR_eq_top_of_not_supportContained _ _ hp]
    simp

/-- The trace-square arithmetic-mean lower bound, retaining unsupported `∞`. -/
theorem flat_pair_mean_lower (P Q : OrthogonalProjector ι)
    (hrP : 0 < P.matrix.rank) (hrQ : 0 < Q.matrix.rank)
    (hrank : P.matrix.rank = Q.matrix.rank)
    (S : Matrix ι ι ℂ) (hHerm : S.IsHermitian) (hSquare : S * S = P.matrix + Q.matrix)
    (σ : Density ι) : ENNReal.ofReal (traceRadius P S) ≤
      (chiR (P.flat hrP) σ + chiR (Q.flat hrQ) σ) / 2 := by
  by_cases hp : SupportContained (P.flat hrP) σ
  · by_cases hq : SupportContained (Q.flat hrQ) σ
    · have ha := flat_pair_average_lower P Q hrP hrQ hrank S hHerm hSquare σ hp hq
      rw [chiR_eq_pinv_trace _ _ hp, chiR_eq_pinv_trace _ _ hq,
        CommonCenter.ofReal_average _ _ (rightEnergy_nonneg _ _) (rightEnergy_nonneg _ _)]
      exact ENNReal.ofReal_le_ofReal ha
    · rw [chiR_eq_top_of_not_supportContained _ _ hq, add_top,
        ENNReal.top_div_of_ne_top (by norm_num)]
      exact le_top
  · rw [chiR_eq_top_of_not_supportContained _ _ hp, top_add,
      ENNReal.top_div_of_ne_top (by norm_num)]
    exact le_top

omit [DecidableEq ι] in
lemma hermitian_trace_real (S : Matrix ι ι ℂ) (hS : S.IsHermitian) :
    ((Matrix.trace S).re : ℂ) = Matrix.trace S := by
  apply Complex.conj_eq_iff_re.mp
  change star (Matrix.trace S) = Matrix.trace S
  rw [← Matrix.trace_conjTranspose, hS.eq]

/-- Normalize any nonzero positive semidefinite matrix, retaining its support. -/
def normalizePSD (S : Matrix ι ι ℂ) (hS : S.PosSemidef)
    (ht : 0 < (Matrix.trace S).re) : Density ι where
  matrix := (((1 / (Matrix.trace S).re : ℝ) : ℂ)) • S
  positive := hS.smul (RCLike.ofReal_nonneg.mpr (one_div_pos.mpr ht).le)
  trace_one := by
    rw [Matrix.trace_smul]
    change (((1 / (Matrix.trace S).re : ℝ) : ℂ)) * Matrix.trace S = 1
    rw [← hermitian_trace_real S hS.1, Complex.ofReal_re, ← Complex.ofReal_mul,
      one_div_mul_cancel (ne_of_gt ht), Complex.ofReal_one]

omit [DecidableEq ι] in
lemma HermitianInverse.smul {A B : Matrix ι ι ℂ} (h : HermitianInverse A B)
    (c : ℝ) (hc : c ≠ 0) :
    HermitianInverse ((c : ℂ) • A) (((c⁻¹ : ℝ) : ℂ) • B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · change (((c⁻¹ : ℝ) : ℂ) • B)ᴴ = _
    simp only [Matrix.conjTranspose_smul, h.hermitian.eq, Complex.star_def, Complex.conj_ofReal]
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.commute]
    congr 1
    ring
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.outer]
    congr 1
    push_cast
    field_simp
  · simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, h.inner]
    congr 1
    push_cast
    field_simp

lemma pinv_normalizePSD (S T : Matrix ι ι ℂ) (hS : S.PosSemidef)
    (ht : 0 < (Matrix.trace S).re) (hT : HermitianInverse S T) :
    pinv (normalizePSD S hS ht) = ((Matrix.trace S).re : ℂ) • T := by
  have hi := hT.smul (1 / (Matrix.trace S).re) (ne_of_gt (one_div_pos.mpr ht))
  simp only [one_div, inv_inv] at hi
  apply (pinv_properties (normalizePSD S hS ht)).unique
    (normalizePSD S hS ht).hermitian
  change HermitianInverse ((((1 / (Matrix.trace S).re : ℝ) : ℂ)) • S)
    (((Matrix.trace S).re : ℂ) • T)
  simpa only [one_div] using hi

omit [DecidableEq ι] in
lemma normalizePSD_kernel (S : Matrix ι ι ℂ) (hS : S.PosSemidef)
    (ht : 0 < (Matrix.trace S).re) (v : ι → ℂ) :
    (normalizePSD S hS ht).matrix *ᵥ v = 0 ↔ S *ᵥ v = 0 := by
  change ((((1 / (Matrix.trace S).re : ℝ) : ℂ)) • S) *ᵥ v = 0 ↔ _
  rw [Matrix.smul_mulVec]
  have hc : (((1 / (Matrix.trace S).re : ℝ) : ℂ)) ≠ 0 := by
    exact_mod_cast ne_of_gt (one_div_pos.mpr ht)
  simp only [smul_eq_zero, hc, false_or]

omit [DecidableEq ι] in
lemma projector_kernel_sum_left (P Q : OrthogonalProjector ι) (v : ι → ℂ)
    (h : (P.matrix + Q.matrix) *ᵥ v = 0) : P.matrix *ᵥ v = 0 := by
  have hp := P.positive.2 v
  have hq := Q.positive.2 v
  have he : star v ⬝ᵥ (P.matrix *ᵥ v) + star v ⬝ᵥ (Q.matrix *ᵥ v) = 0 := by
    rw [← dotProduct_add, ← Matrix.add_mulVec, h, dotProduct_zero]
  have hre := congrArg Complex.re he
  simp only [Complex.add_re, Complex.zero_re] at hre
  have hp0 := hp.1
  have hq0 := hq.1
  simp only [Complex.zero_re] at hp0 hq0
  have hpr : (star v ⬝ᵥ (P.matrix *ᵥ v)).re = 0 := by linarith
  apply (P.positive.dotProduct_mulVec_zero_iff v).mp
  exact Complex.ext hpr hp.2.symm

omit [DecidableEq ι] in
lemma projector_support_normalized_sqrt (P Q : OrthogonalProjector ι)
    (S : Matrix ι ι ℂ) (hS : S.PosSemidef) (ht : 0 < (Matrix.trace S).re)
    (hSquare : S * S = P.matrix + Q.matrix) :
    KernelContained P.matrix (normalizePSD S hS ht).matrix ∧
      KernelContained Q.matrix (normalizePSD S hS ht).matrix := by
  have hm : ∀ v, (normalizePSD S hS ht).matrix *ᵥ v = 0 →
      (P.matrix + Q.matrix) *ᵥ v = 0 := by
    intro v hv
    have hs := (normalizePSD_kernel S hS ht v).mp hv
    rw [← hSquare, ← Matrix.mulVec_mulVec, hs, Matrix.mulVec_zero]
  constructor
  · intro v hv
    exact projector_kernel_sum_left P Q v (hm v hv)
  · intro v hv
    exact projector_kernel_sum_left Q P v (by rw [add_comm]; exact hm v hv)

lemma pinvRisk_normalized_sqrt (S T : Matrix ι ι ℂ) (hS : S.PosSemidef)
    (ht : 0 < (Matrix.trace S).re) (hT : HermitianInverse S T) :
    pinvRisk (S * S) (normalizePSD S hS ht) = (Matrix.trace S).re ^ 2 := by
  unfold pinvRisk
  rw [pinv_normalizePSD S T hS ht hT, Matrix.mul_smul, Matrix.trace_smul]
  have hs : S * S * T = S := by
    rw [Matrix.mul_assoc, hT.commute, ← Matrix.mul_assoc, hT.outer]
  rw [hs]
  simp [smul_eq_mul, Complex.mul_re, pow_two]


lemma principalRadius_nonneg {κ : Type*} [Fintype κ] [Nonempty κ]
    (s : κ → ℝ) (hs : ∀ i, 0 ≤ s i) : 0 ≤ CommonCenter.principalRadius s := by
  have hr : 0 < (Fintype.card κ : ℝ) := by exact_mod_cast Fintype.card_pos
  have hsum : (Fintype.card κ : ℝ) ≤ ∑ i, Real.sqrt (1 + s i) := by
    calc
      (Fintype.card κ : ℝ) = ∑ _i : κ, (1 : ℝ) := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        exact Real.one_le_sqrt.mpr (by linarith [hs i])
  have hd : 1 ≤ (∑ i, Real.sqrt (1 + s i)) / Fintype.card κ :=
    (le_div_iff₀ hr).mpr (by simpa using hsum)
  unfold CommonCenter.principalRadius
  nlinarith

section CanonicalWeak
open CommonCenter

lemma sqrtSum_trace_pos [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    0 < (Matrix.trace (sqrtSum c)).re := by
  rw [sqrtSum_trace c s hcircle hc0 hc1 hs0]
  have hs : 0 < ∑ i, Real.sqrt (1 + s i) := by
    apply Finset.sum_pos
    · intro i _
      exact Real.sqrt_pos.mpr (by linarith [hs0 i])
    · exact Finset.univ_nonempty
  exact mul_pos (Real.sqrt_pos.mpr (by norm_num)) hs

def weakCenter [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    Density (Fin 2 × ι) :=
  normalizePSD (sqrtSum c) (sqrtSum_posSemidef c)
    (sqrtSum_trace_pos c s hcircle hc0 hc1 hs0)

lemma weakCenter_pinv [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    pinv (weakCenter c s hcircle hc0 hc1 hs0) =
      Normalization.diagonalMatrix (fun p => (Matrix.trace (sqrtSum c)).re /
        Real.sqrt (pairSpectrum c p)) := by
  unfold weakCenter
  have hi : HermitianInverse (sqrtSum c)
      (Normalization.diagonalMatrix (fun p => (Real.sqrt (pairSpectrum c p))⁻¹)) :=
    diagonal_inverse_properties (fun p => Real.sqrt (pairSpectrum c p))
  rw [pinv_normalizePSD (sqrtSum c) _ _ _ hi]
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Normalization.diagonalMatrix, Matrix.smul_apply, smul_eq_mul, div_eq_mul_inv]
  · simp [Normalization.diagonalMatrix, Matrix.smul_apply, hij]

lemma weakCenter_support [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    SupportContained (stateP c s hcircle) (weakCenter c s hcircle hc0 hc1 hs0) ∧
      SupportContained (stateQ c s hcircle) (weakCenter c s hcircle hc0 hc1 hs0) := by
  have hpq := projector_support_normalized_sqrt (canonicalP c s hcircle)
    (canonicalQ c s hcircle) (sqrtSum c) (sqrtSum_posSemidef c)
    (sqrtSum_trace_pos c s hcircle hc0 hc1 hs0) (sqrtSum_square c s hcircle hc0 hc1)
  constructor
  · intro v hv
    apply (CommonCenter.flat_kernel _ _ v).mpr
    exact hpq.1 v hv
  · intro v hv
    apply (CommonCenter.flat_kernel _ _ v).mpr
    exact hpq.2 v hv

lemma weakCenter_risks_equal [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    pinvRisk (canonicalP c s hcircle).matrix (weakCenter c s hcircle hc0 hc1 hs0) =
      pinvRisk (canonicalQ c s hcircle).matrix (weakCenter c s hcircle hc0 hc1 hs0) := by
  unfold pinvRisk
  rw [weakCenter_pinv]
  congr 1
  simp only [Matrix.trace, Matrix.diag, Normalization.diagonalMatrix, Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro p _
  rw [canonical_diagonal_equal]

/-- Actual singular square-root center losses, including all zero principal
angles. No positive-definiteness assumption is needed. -/
theorem weakCenter_losses [Nonempty ι] (c s : ι → ℝ)
    (hcircle : ∀ i, c i ^ 2 + s i ^ 2 = 1)
    (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1) (hs0 : ∀ i, 0 ≤ s i) :
    chiR (stateP c s hcircle) (weakCenter c s hcircle hc0 hc1 hs0) =
        ENNReal.ofReal (principalRadius s) ∧
      chiR (stateQ c s hcircle) (weakCenter c s hcircle hc0 hc1 hs0) =
        ENNReal.ofReal (principalRadius s) := by
  let A := weakCenter c s hcircle hc0 hc1 hs0
  obtain ⟨hp, hq⟩ := weakCenter_support c s hcircle hc0 hc1 hs0
  have hsum : pinvRisk ((canonicalP c s hcircle).matrix +
      (canonicalQ c s hcircle).matrix) A = (Matrix.trace (sqrtSum c)).re ^ 2 := by
    rw [← sqrtSum_square c s hcircle hc0 hc1]
    exact pinvRisk_normalized_sqrt _ _ _ _
      (diagonal_inverse_properties (fun p => Real.sqrt (pairSpectrum c p)))
  have heq := weakCenter_risks_equal c s hcircle hc0 hc1 hs0
  change pinvRisk _ A = pinvRisk _ A at heq
  have hP := flat_rightEnergy (canonicalP c s hcircle) _ A hp
  have hQ := flat_rightEnergy (canonicalQ c s hcircle) _ A hq
  rw [canonicalP_rank] at hP
  rw [canonicalQ_rank] at hQ
  rw [pinvRisk_add] at hsum
  have hform := principalRadius_trace_formula c s hcircle hc0 hc1 hs0
  have hEP : rightEnergy (stateP c s hcircle) A = principalRadius s := by
    change rightEnergy (stateP c s hcircle) A = _ at hP
    nlinarith [hP, hform]
  have hEQ : rightEnergy (stateQ c s hcircle) A = principalRadius s := by
    change rightEnergy (stateQ c s hcircle) A = _ at hQ
    nlinarith [hQ, hform]
  exact ⟨(chiR_eq_pinv_trace _ _ hp).trans (congrArg ENNReal.ofReal hEP),
    (chiR_eq_pinv_trace _ _ hq).trans (congrArg ENNReal.ofReal hEQ)⟩

end CanonicalWeak

section Isometry
variable {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- Actual rectangular isometric embedding, permitting a larger ambient space. -/
def embedMatrix (V : Matrix ι κ ℂ) (X : Matrix κ κ ℂ) : Matrix ι ι ℂ := V * X * Vᴴ

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma embedMatrix_add (V : Matrix ι κ ℂ) (X Y : Matrix κ κ ℂ) :
    embedMatrix V (X + Y) = embedMatrix V X + embedMatrix V Y := by
  simp [embedMatrix, Matrix.mul_add, Matrix.add_mul]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma embedMatrix_sub (V : Matrix ι κ ℂ) (X Y : Matrix κ κ ℂ) :
    embedMatrix V (X - Y) = embedMatrix V X - embedMatrix V Y := by
  simp [embedMatrix, Matrix.mul_sub, Matrix.sub_mul]

omit [DecidableEq ι] in
lemma embedMatrix_mul (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (X Y : Matrix κ κ ℂ) :
    embedMatrix V (X * Y) = embedMatrix V X * embedMatrix V Y := by
  unfold embedMatrix
  calc
    V * (X * Y) * Vᴴ = V * X * (Vᴴ * V) * Y * Vᴴ := by
      rw [hV]
      simp only [Matrix.mul_one, Matrix.mul_assoc]
    _ = _ := by simp only [Matrix.mul_assoc]

omit [DecidableEq ι] in
lemma embedMatrix_trace (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (X : Matrix κ κ ℂ) :
    Matrix.trace (embedMatrix V X) = Matrix.trace X := by
  rw [embedMatrix, Matrix.trace_mul_cycle, hV, Matrix.one_mul]


omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma embedMatrix_conjTranspose (V : Matrix ι κ ℂ) (X : Matrix κ κ ℂ) :
    (embedMatrix V X)ᴴ = embedMatrix V Xᴴ := by
  simp only [embedMatrix, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    Matrix.mul_assoc]

lemma cfc_sqrt_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (X : Matrix κ κ ℂ) (hX : X.PosSemidef) :
    CFC.sqrt (embedMatrix V X) = embedMatrix V (CFC.sqrt X) := by
  apply CFC.sqrt_unique
  · rw [← embedMatrix_mul V hV, CFC.sqrt_mul_sqrt_self X hX.nonneg]
  · exact ((Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg X)).mul_mul_conjTranspose_same V).nonneg

lemma traceNorm_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (X : Matrix κ κ ℂ) :
    CommonCenter.traceNorm (embedMatrix V X) = CommonCenter.traceNorm X := by
  unfold CommonCenter.traceNorm
  rw [embedMatrix_conjTranspose, ← embedMatrix_mul V hV,
    cfc_sqrt_embed V hV _ (Matrix.posSemidef_conjTranspose_mul_self X),
    embedMatrix_trace V hV]

omit [DecidableEq ι] in
lemma HermitianInverse.isometry {A B : Matrix κ κ ℂ} (h : HermitianInverse A B)
    (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) :
    HermitianInverse (embedMatrix V A) (embedMatrix V B) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [embedMatrix] using Matrix.isHermitian_mul_mul_conjTranspose V h.hermitian
  · rw [← embedMatrix_mul V hV, ← embedMatrix_mul V hV, h.commute]
  · rw [← embedMatrix_mul V hV, ← embedMatrix_mul V hV, h.outer]
  · rw [← embedMatrix_mul V hV, ← embedMatrix_mul V hV, h.inner]

/-- Isometric embedding preserves actual positivity and trace one. -/
def embedDensity (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (ρ : Density κ) : Density ι where
  matrix := embedMatrix V ρ.matrix
  positive := ρ.positive.mul_mul_conjTranspose_same V
  trace_one := by rw [embedMatrix_trace V hV, ρ.trace_one]

omit [DecidableEq ι] in
@[simp] theorem embedDensity_matrix (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (ρ : Density κ) : (embedDensity V hV ρ).matrix = embedMatrix V ρ.matrix := rfl

lemma pinv_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (σ : Density κ) :
    pinv (embedDensity V hV σ) = embedMatrix V (pinv σ) := by
  exact (pinv_properties (embedDensity V hV σ)).unique (embedDensity V hV σ).hermitian
    ((pinv_properties σ).isometry V hV)

omit [DecidableEq ι] in
lemma supportContained_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (ρ σ : Density κ) :
    SupportContained (embedDensity V hV ρ) (embedDensity V hV σ) ↔ SupportContained ρ σ := by
  have hinj : Function.Injective (fun w : κ → ℂ => V *ᵥ w) := by
    intro v w h
    have ht := congrArg (fun x => Vᴴ *ᵥ x) h
    change Vᴴ *ᵥ (V *ᵥ v) = Vᴴ *ᵥ (V *ᵥ w) at ht
    simpa only [Matrix.mulVec_mulVec, hV, Matrix.one_mulVec] using ht
  constructor
  · intro h v hv
    have hs : (embedDensity V hV σ).matrix *ᵥ (V *ᵥ v) = 0 := by
      change (V * σ.matrix * Vᴴ) *ᵥ (V *ᵥ v) = 0
      rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec v Vᴴ V, hV,
        Matrix.one_mulVec, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]
    have hr := h (V *ᵥ v) hs
    change (V * ρ.matrix * Vᴴ) *ᵥ (V *ᵥ v) = 0 at hr
    rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec v Vᴴ V, hV,
      Matrix.one_mulVec, ← Matrix.mulVec_mulVec] at hr
    exact hinj (hr.trans (Matrix.mulVec_zero V).symm)
  · intro h v hv
    change (V * σ.matrix * Vᴴ) *ᵥ v = 0 at hv
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec] at hv
    have hs : σ.matrix *ᵥ (Vᴴ *ᵥ v) = 0 := hinj (hv.trans (Matrix.mulVec_zero V).symm)
    have hr := h (Vᴴ *ᵥ v) hs
    change (V * ρ.matrix * Vᴴ) *ᵥ v = 0
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hr, Matrix.mulVec_zero]

lemma rightEnergy_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (ρ σ : Density κ) :
    rightEnergy (embedDensity V hV ρ) (embedDensity V hV σ) = rightEnergy ρ σ := by
  unfold rightEnergy
  simp only [embedDensity_matrix]
  rw [pinv_embed, ← embedMatrix_sub, ← embedMatrix_mul V hV,
    ← embedMatrix_mul V hV, embedMatrix_trace V hV]

/-- Exact support compression of actual χR through a rectangular isometry,
including the infinite-loss branch and arbitrary ambient orthogonal complements. -/
theorem chiR_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1) (ρ σ : Density κ) :
    chiR (embedDensity V hV ρ) (embedDensity V hV σ) = chiR ρ σ := by
  by_cases h : SupportContained ρ σ
  · rw [chiR_eq_pinv_trace _ _ ((supportContained_embed V hV ρ σ).mpr h),
      chiR_eq_pinv_trace ρ σ h, rightEnergy_embed]
  · have hc := mt (supportContained_embed V hV ρ σ).mp h
    rw [chiR_eq_top_of_not_supportContained _ _ hc,
      chiR_eq_top_of_not_supportContained _ _ h]


lemma projector_rank_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (P : OrthogonalProjector ι) (Q : OrthogonalProjector κ)
    (hP : P.matrix = embedMatrix V Q.matrix) : P.matrix.rank = Q.matrix.rank := by
  have ht : (P.matrix.rank : ℂ) = (Q.matrix.rank : ℂ) := by
    rw [← P.trace_eq_rank, hP, embedMatrix_trace V hV, Q.trace_eq_rank]
  exact_mod_cast ht

lemma flat_embed (V : Matrix ι κ ℂ) (hV : Vᴴ * V = 1)
    (P : OrthogonalProjector ι) (Q : OrthogonalProjector κ)
    (hP : P.matrix = embedMatrix V Q.matrix) (hrP : 0 < P.matrix.rank)
    (hrQ : 0 < Q.matrix.rank) : P.flat hrP = embedDensity V hV (Q.flat hrQ) := by
  apply CommonCenter.density_eq_of_matrix
  have hr := projector_rank_embed V hV P Q hP
  change ((P.matrix.rank : ℝ)⁻¹) • P.matrix =
    embedMatrix V (((Q.matrix.rank : ℝ)⁻¹) • Q.matrix)
  rw [hr, hP]
  simp only [embedMatrix, Matrix.mul_smul, Matrix.smul_mul]

end Isometry


section FullPrincipalAngles
variable {κ : Type*} [Fintype κ] [DecidableEq κ]
open CommonCenter

/-- Raw principal-angle decomposition in an arbitrary ambient dimension. The
matrix `isometry` has `2r` orthonormal columns; extra ambient directions vanish.
Zero principal angles are allowed. The input contains no loss or center claim. -/
structure PrincipalAngleForm (P Q : OrthogonalProjector ι) where
  c : κ → ℝ
  s : κ → ℝ
  circle : ∀ i, c i ^ 2 + s i ^ 2 = 1
  cosine_nonneg : ∀ i, 0 ≤ c i
  cosine_le_one : ∀ i, c i ≤ 1
  sine_nonneg : ∀ i, 0 ≤ s i
  isometry : Matrix ι (Fin 2 × κ) ℂ
  orthonormal : isometryᴴ * isometry = 1
  first : P.matrix = embedMatrix isometry (canonicalP c s circle).matrix
  second : Q.matrix = embedMatrix isometry (canonicalQ c s circle).matrix

namespace PrincipalAngleForm
variable {P Q : OrthogonalProjector ι}

lemma rankP (D : PrincipalAngleForm (κ := κ) P Q) : P.matrix.rank = Fintype.card κ := by
  rw [projector_rank_embed D.isometry D.orthonormal P _ D.first, canonicalP_rank]

lemma rankQ (D : PrincipalAngleForm (κ := κ) P Q) : Q.matrix.rank = Fintype.card κ := by
  rw [projector_rank_embed D.isometry D.orthonormal Q _ D.second, canonicalQ_rank]

def root (D : PrincipalAngleForm (κ := κ) P Q) : Matrix ι ι ℂ :=
  embedMatrix D.isometry (sqrtSum D.c)

omit [DecidableEq ι] in
lemma root_positive (D : PrincipalAngleForm (κ := κ) P Q) : D.root.PosSemidef :=
  (sqrtSum_posSemidef D.c).mul_mul_conjTranspose_same D.isometry

omit [DecidableEq ι] in
lemma root_square (D : PrincipalAngleForm (κ := κ) P Q) :
    D.root * D.root = P.matrix + Q.matrix := by
  unfold root
  rw [← embedMatrix_mul D.isometry D.orthonormal,
    sqrtSum_square D.c D.s D.circle D.cosine_nonneg D.cosine_le_one,
    embedMatrix_add, ← D.first, ← D.second]

lemma cfc_sqrt_sum (D : PrincipalAngleForm (κ := κ) P Q) :
    CFC.sqrt (P.matrix + Q.matrix) = D.root :=
  CFC.sqrt_unique D.root_square D.root_positive.nonneg

omit [DecidableEq ι] in
lemma root_trace (D : PrincipalAngleForm (κ := κ) P Q) :
    Matrix.trace D.root = Matrix.trace (sqrtSum D.c) :=
  embedMatrix_trace D.isometry D.orthonormal _

lemma sqrt_trace_formula (D : PrincipalAngleForm (κ := κ) P Q) :
    (Matrix.trace (CFC.sqrt (P.matrix + Q.matrix))).re =
      Real.sqrt 2 * ∑ i, Real.sqrt (1 + D.s i) := by
  rw [D.cfc_sqrt_sum, D.root_trace]
  exact sqrtSum_trace D.c D.s D.circle D.cosine_nonneg D.cosine_le_one D.sine_nonneg

variable [Nonempty κ]

lemma rankP_pos (D : PrincipalAngleForm (κ := κ) P Q) : 0 < P.matrix.rank := by
  rw [D.rankP]
  exact Fintype.card_pos

lemma rankQ_pos (D : PrincipalAngleForm (κ := κ) P Q) : 0 < Q.matrix.rank := by
  rw [D.rankQ]
  exact Fintype.card_pos

lemma flatP (D : PrincipalAngleForm (κ := κ) P Q) : P.flat D.rankP_pos =
    embedDensity D.isometry D.orthonormal (stateP D.c D.s D.circle) :=
  flat_embed D.isometry D.orthonormal P _ D.first _ _

lemma flatQ (D : PrincipalAngleForm (κ := κ) P Q) : Q.flat D.rankQ_pos =
    embedDensity D.isometry D.orthonormal (stateQ D.c D.s D.circle) :=
  flat_embed D.isometry D.orthonormal Q _ D.second _ _

def center (D : PrincipalAngleForm (κ := κ) P Q) : Density ι :=
  embedDensity D.isometry D.orthonormal
    (weakCenter D.c D.s D.circle D.cosine_nonneg D.cosine_le_one D.sine_nonneg)

lemma center_losses (D : PrincipalAngleForm (κ := κ) P Q) :
    chiR (P.flat D.rankP_pos) D.center = ENNReal.ofReal (principalRadius D.s) ∧
      chiR (Q.flat D.rankQ_pos) D.center = ENNReal.ofReal (principalRadius D.s) := by
  rw [D.flatP, D.flatQ]
  unfold center
  rw [chiR_embed, chiR_embed]
  exact weakCenter_losses D.c D.s D.circle D.cosine_nonneg D.cosine_le_one D.sine_nonneg

lemma traceRadius_eq (D : PrincipalAngleForm (κ := κ) P Q) :
    traceRadius P D.root = principalRadius D.s := by
  unfold traceRadius
  rw [D.rankP, D.root_trace]
  exact principalRadius_trace_formula D.c D.s D.circle D.cosine_nonneg
    D.cosine_le_one D.sine_nonneg

lemma max_lower (D : PrincipalAngleForm (κ := κ) P Q) (A : Density ι) :
    ENNReal.ofReal (principalRadius D.s) ≤
      max (chiR (P.flat D.rankP_pos) A) (chiR (Q.flat D.rankQ_pos) A) := by
  rw [← D.traceRadius_eq]
  exact flat_pair_max_lower P Q D.rankP_pos D.rankQ_pos
    (D.rankP.trans D.rankQ.symm) D.root D.root_positive.1 D.root_square A

lemma mean_lower (D : PrincipalAngleForm (κ := κ) P Q) (A : Density ι) :
    ENNReal.ofReal (principalRadius D.s) ≤
      (chiR (P.flat D.rankP_pos) A + chiR (Q.flat D.rankQ_pos) A) / 2 := by
  rw [← D.traceRadius_eq]
  exact flat_pair_mean_lower P Q D.rankP_pos D.rankQ_pos
    (D.rankP.trans D.rankQ.symm) D.root D.root_positive.1 D.root_square A

/-- Full Proposition B.1 minimax equality from raw standard principal-angle
block data, allowing zero angles, singular centers, and ambient complements. -/
theorem minimax (D : PrincipalAngleForm (κ := κ) P Q) :
    (⨅ A : Density ι, max (chiR (P.flat D.rankP_pos) A) (chiR (Q.flat D.rankQ_pos) A)) =
      ENNReal.ofReal (principalRadius D.s) := by
  apply le_antisymm
  · apply iInf_le_of_le D.center
    obtain ⟨hp, hq⟩ := D.center_losses
    rw [hp, hq, max_self]
  · exact le_iInf D.max_lower

/-- The same singular square-root center attains the minimum arithmetic mean. -/
theorem mean (D : PrincipalAngleForm (κ := κ) P Q) :
    (⨅ A : Density ι, (chiR (P.flat D.rankP_pos) A + chiR (Q.flat D.rankQ_pos) A) / 2) =
      ENNReal.ofReal (principalRadius D.s) := by
  apply le_antisymm
  · apply iInf_le_of_le D.center
    obtain ⟨hp, hq⟩ := D.center_losses
    have hr := principalRadius_nonneg D.s D.sine_nonneg
    rw [hp, hq, CommonCenter.ofReal_average _ _ hr hr]
    have he : (principalRadius D.s + principalRadius D.s) / 2 = principalRadius D.s := by ring
    rw [he]
  · exact le_iInf D.mean_lower


/-- The constructed center is the original-basis normalized positive square
root even when it is singular and the ambient space has an unused complement. -/
lemma center_matrix (D : PrincipalAngleForm (κ := κ) P Q) :
    D.center.matrix = ((1 / (Matrix.trace (CFC.sqrt (P.matrix + Q.matrix))).re : ℝ) : ℂ) •
      CFC.sqrt (P.matrix + Q.matrix) := by
  rw [D.cfc_sqrt_sum, D.root_trace]
  unfold center embedDensity weakCenter normalizePSD root
  simp only [embedMatrix, Matrix.mul_smul, Matrix.smul_mul]

omit [Nonempty κ] in
lemma traceNorm_difference (D : PrincipalAngleForm (κ := κ) P Q) :
    traceNorm (P.matrix - Q.matrix) = 2 * ∑ i, D.s i := by
  rw [D.first, D.second, ← embedMatrix_sub, traceNorm_embed D.isometry D.orthonormal,
    canonical_traceNorm D.c D.s D.circle D.sine_nonneg]

lemma chord (D : PrincipalAngleForm (κ := κ) P Q) :
    (Real.sqrt 2 - 1) * traceNorm (P.matrix - Q.matrix) / Fintype.card κ ≤
      principalRadius D.s := by
  have h := principalRadius_traceNorm_lower D.c D.s D.circle D.sine_nonneg
  rw [canonical_traceNorm D.c D.s D.circle D.sine_nonneg] at h
  rwa [D.traceNorm_difference]

theorem minimax_chord (D : PrincipalAngleForm (κ := κ) P Q) :
    ENNReal.ofReal ((Real.sqrt 2 - 1) * traceNorm (P.matrix - Q.matrix) / Fintype.card κ) ≤
      ⨅ A : Density ι, max (chiR (P.flat D.rankP_pos) A) (chiR (Q.flat D.rankQ_pos) A) := by
  rw [D.minimax]
  exact ENNReal.ofReal_le_ofReal D.chord

theorem mean_chord (D : PrincipalAngleForm (κ := κ) P Q) :
    ENNReal.ofReal ((Real.sqrt 2 - 1) * traceNorm (P.matrix - Q.matrix) / Fintype.card κ) ≤
      ⨅ A : Density ι, (chiR (P.flat D.rankP_pos) A + chiR (Q.flat D.rankQ_pos) A) / 2 := by
  rw [D.mean]
  exact ENNReal.ofReal_le_ofReal D.chord

end PrincipalAngleForm
end FullPrincipalAngles


/-- Exact standard principal-angle block decomposition input. Its content is
only rectangular matrix isometry and the two explicit rank-one block forms.
There are no χ², trace-norm, fidelity, or optimal-center conclusions here. -/
def PrincipalAngleDecompositionInput : Prop :=
  ∀ (r : ℕ) (P Q : OrthogonalProjector ι), 0 < r →
    P.matrix.rank = r → Q.matrix.rank = r → 2 * r ≤ Fintype.card ι →
      Nonempty (PrincipalAngleForm (κ := Fin r) P Q)

/-- Proposition B.1 in intrinsic matrix form for every positive common rank,
including coincident subspaces and ambient complements. The sole classical
input is the explicitly stated raw principal-angle decomposition theorem. -/
theorem proposition_B_1 (angles : PrincipalAngleDecompositionInput (ι := ι))
    (P Q : OrthogonalProjector ι) (hrP : 0 < P.matrix.rank) (hrQ : 0 < Q.matrix.rank)
    (hrank : P.matrix.rank = Q.matrix.rank) (hdim : 2 * P.matrix.rank ≤ Fintype.card ι) :
    ∃ σ : Density ι,
      σ.matrix = (((1 / (Matrix.trace (CFC.sqrt (P.matrix + Q.matrix))).re : ℝ) : ℂ) •
        CFC.sqrt (P.matrix + Q.matrix)) ∧
      chiR (P.flat hrP) σ = ENNReal.ofReal (traceRadius P (CFC.sqrt (P.matrix + Q.matrix))) ∧
      chiR (Q.flat hrQ) σ = ENNReal.ofReal (traceRadius P (CFC.sqrt (P.matrix + Q.matrix))) ∧
      (⨅ A : Density ι, max (chiR (P.flat hrP) A) (chiR (Q.flat hrQ) A)) =
        ENNReal.ofReal (traceRadius P (CFC.sqrt (P.matrix + Q.matrix))) ∧
      (⨅ A : Density ι, (chiR (P.flat hrP) A + chiR (Q.flat hrQ) A) / 2) =
        ENNReal.ofReal (traceRadius P (CFC.sqrt (P.matrix + Q.matrix))) ∧
      ENNReal.ofReal ((Real.sqrt 2 - 1) * CommonCenter.traceNorm (P.matrix - Q.matrix) /
        P.matrix.rank) ≤ ENNReal.ofReal (traceRadius P (CFC.sqrt (P.matrix + Q.matrix))) := by
  letI : NeZero P.matrix.rank := ⟨ne_of_gt hrP⟩
  obtain ⟨D⟩ := angles P.matrix.rank P Q hrP rfl hrank.symm hdim
  have hv : traceRadius P (CFC.sqrt (P.matrix + Q.matrix)) = CommonCenter.principalRadius D.s := by
    rw [D.cfc_sqrt_sum]
    exact D.traceRadius_eq
  refine ⟨D.center, D.center_matrix, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hv]
    exact D.center_losses.1
  · rw [hv]
    exact D.center_losses.2
  · rw [hv]
    exact D.minimax
  · rw [hv]
    exact D.mean
  · rw [hv]
    apply ENNReal.ofReal_le_ofReal
    simpa only [Fintype.card_fin] using D.chord

end Paper26.SupportCompression
