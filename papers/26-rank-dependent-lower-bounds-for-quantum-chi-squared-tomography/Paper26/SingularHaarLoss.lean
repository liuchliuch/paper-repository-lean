import Paper26.HaarTruncation

/-!
# Singular-output successful sets are Haar-null

The only external input is the generic Haar column-range nullity proposition
`HaarTruncation.ProperSubspaceNullInput`. The passage from the actual
chi-squared losses to a fixed proper subspace is proved here: a singular
density has a nonzero kernel vector; finite loss gives the defined reverse
kernel inclusion; and the flat frame state has exactly the kernel of `Uᴴ`.
No singular-loss nullity or finite-loss support assertion is an external field.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.SingularHaarLoss

open QuantumModel HaarFrames HaarTruncation

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype κ] [DecidableEq κ] [Nonempty κ]

/-- Orthogonal complement of the actual kernel of a matrix, in the standard
complex coordinate pairing. It is a genuine complex linear submodule. -/
def kernelOrthogonal (A : Matrix ι ι ℂ) : Submodule ℂ (ι → ℂ) where
  carrier := {y | ∀ x : ι → ℂ, A *ᵥ x = 0 → star x ⬝ᵥ y = 0}
  zero_mem' := by intro x _; exact dotProduct_zero _
  add_mem' := by
    intro y z hy hz x hx
    rw [dotProduct_add, hy x hx, hz x hx, add_zero]
  smul_mem' := by
    intro c y hy x hx
    rw [dotProduct_smul, hy x hx, smul_zero]

@[simp] theorem mem_kernelOrthogonal (A : Matrix ι ι ℂ) (y : ι → ℂ) :
    y ∈ kernelOrthogonal A ↔
      ∀ x : ι → ℂ, A *ᵥ x = 0 → star x ⬝ᵥ y = 0 := Iff.rfl

/-- Native Hermitian spectral theory and positivity give an actual nonzero
kernel vector for every density which is not positive definite. -/
theorem singular_density_has_kernel (τ : Density ι) (hsing : ¬ τ.matrix.PosDef) :
    ∃ x : ι → ℂ, x ≠ 0 ∧ τ.matrix *ᵥ x = 0 := by
  classical
  have hn : ¬ ∀ i, 0 < τ.hermitian.eigenvalues i := by
    intro h
    exact hsing (τ.hermitian.posDef_iff_eigenvalues_pos.2 h)
  obtain ⟨i, hi⟩ := not_forall.mp hn
  have he : τ.hermitian.eigenvalues i = 0 :=
    le_antisymm (le_of_not_gt hi) (τ.positive.eigenvalues_nonneg i)
  refine ⟨τ.hermitian.eigenvectorBasis i,
    τ.hermitian.eigenvectorBasis.orthonormal.ne_zero i, ?_⟩
  simpa only [he, zero_smul] using τ.hermitian.mulVec_eigenvectorBasis i

/-- The fixed kernel-orthogonal submodule is proper for singular outputs. -/
theorem kernelOrthogonal_ne_top (τ : Density ι) (hsing : ¬ τ.matrix.PosDef) :
    kernelOrthogonal τ.matrix ≠ ⊤ := by
  obtain ⟨x, hx, hker⟩ := singular_density_has_kernel τ hsing
  intro htop
  have hmem : x ∈ kernelOrthogonal τ.matrix := by
    rw [htop]
    exact Submodule.mem_top
  have hself : star x ⬝ᵥ x = 0 := hmem x hker
  exact hx (dotProduct_star_self_eq_zero.1 hself)

/-- A flat frame density has the kernel of the actual adjoint frame matrix.
The normalization scalar is nonzero because the column type is nonempty. -/
theorem frame_density_kernel (U : Frame ι κ) (x : ι → ℂ) :
    U.density.matrix *ᵥ x = 0 ↔ U.matrixᴴ *ᵥ x = 0 := by
  have hc : (Fintype.card κ : ℝ)⁻¹ ≠ 0 :=
    inv_ne_zero (Nat.cast_ne_zero.2 (Nat.ne_of_gt Fintype.card_pos))
  rw [Frame.density_matrix, Matrix.smul_mulVec, smul_eq_zero]
  simp only [hc, false_or]
  exact Matrix.self_mul_conjTranspose_mulVec_eq_zero U.matrix x

/-- Every vector in the frame's actual column range is orthogonal to every
output-kernel vector, whenever the defined support inclusion holds. -/
theorem support_contained_columns (U : Frame ι κ) (τ : Density ι)
    (hsupport : SupportContained U.density τ) :
    ∀ v : κ → ℂ, U.matrix *ᵥ v ∈ kernelOrthogonal τ.matrix := by
  intro v x hx
  have hflat : U.density.matrix *ᵥ x = 0 := hsupport x hx
  have hadj : U.matrixᴴ *ᵥ x = 0 := (frame_density_kernel U x).1 hflat
  have hrow : star x ᵥ* U.matrix = 0 := by
    have h := congrArg star hadj
    simpa only [Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose, star_zero] using h
  rw [Matrix.dotProduct_mulVec, hrow, zero_dotProduct]

/-- The actual finite-support event for a fixed output. -/
def supportedFrames (τ : Density ι) : Set (Frame ι κ) :=
  {U | SupportContained U.density τ}

/-- The generic proper-subspace Haar fact applies after all support and
matrix-kernel deductions have been proved locally. -/
theorem supportedFrames_null (N : ProperSubspaceNullInput ι κ)
    (μ : Measure (Frame ι κ)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density ι) (hsing : ¬ τ.matrix.PosDef) : μ (supportedFrames τ) = 0 := by
  apply event_null_of_column_containment N μ hμ (kernelOrthogonal τ.matrix)
    (kernelOrthogonal_ne_top τ hsing) (supportedFrames τ)
  intro U hU
  exact support_contained_columns U τ hU

/-- The actual Bures finite-loss event is null for every singular output. -/
theorem chiB_finite_null (N : ProperSubspaceNullInput ι κ)
    (μ : Measure (Frame ι κ)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density ι) (hsing : ¬ τ.matrix.PosDef) :
    μ {U : Frame ι κ | chiB U.density τ ≠ ∞} = 0 := by
  simpa only [chiB_ne_top_iff, supportedFrames] using supportedFrames_null N μ hμ τ hsing

/-- The same statement for the actual right-inverse finite-loss event. -/
theorem chiR_finite_null (N : ProperSubspaceNullInput ι κ)
    (μ : Measure (Frame ι κ)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density ι) (hsing : ¬ τ.matrix.PosDef) :
    μ {U : Frame ι κ | chiR U.density τ ≠ ∞} = 0 := by
  simpa only [chiR_ne_top_iff, supportedFrames] using supportedFrames_null N μ hμ τ hsing

/-- The Bures successful-loss set for a singular density output is Haar-null.
There is no measurability restriction on the event: this is outer nullity. -/
theorem chiB_success_null (N : ProperSubspaceNullInput ι κ)
    (μ : Measure (Frame ι κ)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density ι) (hsing : ¬ τ.matrix.PosDef) (ε : ℝ) :
    μ {U : Frame ι κ | chiB U.density τ ≤ ENNReal.ofReal ε} = 0 := by
  have hsub : {U : Frame ι κ | chiB U.density τ ≤ ENNReal.ofReal ε} ⊆
      {U : Frame ι κ | chiB U.density τ ≠ ∞} := by
    intro U hU
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU
  have h := measure_mono (μ := μ) hsub
  rw [chiB_finite_null N μ hμ τ hsing] at h
  exact le_antisymm h (zero_le _)

/-- The right-inverse successful-loss set for the same singular density
output is Haar-null, relative only to generic Haar subspace nullity. -/
theorem chiR_success_null (N : ProperSubspaceNullInput ι κ)
    (μ : Measure (Frame ι κ)) (hμ : IsHaarFrameDistribution μ)
    (τ : Density ι) (hsing : ¬ τ.matrix.PosDef) (ε : ℝ) :
    μ {U : Frame ι κ | chiR U.density τ ≤ ENNReal.ofReal ε} = 0 := by
  have hsub : {U : Frame ι κ | chiR U.density τ ≤ ENNReal.ofReal ε} ⊆
      {U : Frame ι κ | chiR U.density τ ≠ ∞} := by
    intro U hU
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hU
  have h := measure_mono (μ := μ) hsub
  rw [chiR_finite_null N μ hμ τ hsing] at h
  exact le_antisymm h (zero_le _)

end Paper26.SingularHaarLoss
