import PsgEst.Basic
import Mathlib.Data.Real.StarOrdered

/-! The concrete regularizer `(H + τ I)⁻¹ᐟ²` used in the matrix martingale.
It is defined by the Hermitian spectral basis, rather than by assumptions on
an unspecified normalizing matrix. -/

open Matrix BigOperators Real

namespace PsgEst

section Regularizer

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  {H : Matrix ι ι ℝ}

/-- A real diagonal multiplier transported through the actual orthonormal
    eigenbasis of `H`. -/
noncomputable def spectralMultiplier (hH : H.IsHermitian) (f : ι → ℝ) : Matrix ι ι ℝ :=
  (hH.eigenvectorUnitary : Matrix ι ι ℝ) * Matrix.diagonal f *
    (hH.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ

private theorem spectral_unitary_left (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ *
      (hH.eigenvectorUnitary : Matrix ι ι ℝ) = 1 :=
  unitary.coe_star_mul_self hH.eigenvectorUnitary

private theorem spectral_unitary_right (hH : H.IsHermitian) :
    (hH.eigenvectorUnitary : Matrix ι ι ℝ) *
      (hH.eigenvectorUnitary : Matrix ι ι ℝ)ᴴ = 1 :=
  unitary.coe_mul_star_self hH.eigenvectorUnitary

@[simp] theorem spectralMultiplier_one (hH : H.IsHermitian) :
    spectralMultiplier hH (fun _ => 1) = 1 := by
  simp only [spectralMultiplier, Matrix.diagonal_one, Matrix.mul_one,
    spectral_unitary_right]

@[simp] theorem spectralMultiplier_eigenvalues (hH : H.IsHermitian) :
    spectralMultiplier hH hH.eigenvalues = H := by
  simpa [spectralMultiplier] using hH.spectral_theorem.symm

theorem spectralMultiplier_mul (hH : H.IsHermitian) (f g : ι → ℝ) :
    spectralMultiplier hH f * spectralMultiplier hH g =
      spectralMultiplier hH (fun i => f i * g i) := by
  let U : Matrix ι ι ℝ := hH.eigenvectorUnitary
  change (U * Matrix.diagonal f * Uᴴ) * (U * Matrix.diagonal g * Uᴴ) = _
  calc
    _ = U * Matrix.diagonal f * (Uᴴ * U) * Matrix.diagonal g * Uᴴ := by
      noncomm_ring
    _ = U * (Matrix.diagonal f * Matrix.diagonal g) * Uᴴ := by
      rw [spectral_unitary_left hH]
      simp [Matrix.mul_assoc]
    _ = spectralMultiplier hH (fun i => f i * g i) := by
      rw [Matrix.diagonal_mul_diagonal]
      rfl

theorem spectralMultiplier_add (hH : H.IsHermitian) (f g : ι → ℝ) :
    spectralMultiplier hH (fun i => f i + g i) =
      spectralMultiplier hH f + spectralMultiplier hH g := by
  simp only [spectralMultiplier, ← Matrix.diagonal_add, Matrix.mul_add, Matrix.add_mul]

theorem spectralMultiplier_const (hH : H.IsHermitian) (c : ℝ) :
    spectralMultiplier hH (fun _ => c) = c • (1 : Matrix ι ι ℝ) := by
  have hf : (fun _ : ι => c) = c • (fun _ : ι => (1:ℝ)) := by
    ext i
    simp
  rw [hf]
  simp only [spectralMultiplier, Matrix.diagonal_smul, Matrix.mul_smul,
    Matrix.smul_mul, Matrix.diagonal_one, Matrix.mul_one, spectral_unitary_right]

theorem spectralMultiplier_isHermitian (hH : H.IsHermitian) (f : ι → ℝ) :
    (spectralMultiplier hH f).IsHermitian :=
  Matrix.isHermitian_mul_mul_conjTranspose _ (Matrix.isHermitian_diagonal f)

/-- The paper's regularizer `A = (H + τ I)⁻¹ᐟ²`, with every multiplier
    explicitly equal to `1 / sqrt (λ_i(H) + τ)`. -/
noncomputable def regularizer (hH : H.IsHermitian) (τ : ℝ) : Matrix ι ι ℝ :=
  spectralMultiplier hH (fun i => (Real.sqrt (hH.eigenvalues i + τ))⁻¹)

/-- Explicit inverse of the regularizer. -/
noncomputable def regularizerInverse (hH : H.IsHermitian) (τ : ℝ) : Matrix ι ι ℝ :=
  spectralMultiplier hH (fun i => Real.sqrt (hH.eigenvalues i + τ))

theorem regularizer_isHermitian (hH : H.IsHermitian) (τ : ℝ) :
    (regularizer hH τ).IsHermitian := spectralMultiplier_isHermitian _ _

/-- Positivity of the inverse square root is part of the construction. -/
theorem regularizer_posSemidef (hH : H.IsHermitian) (τ : ℝ) :
    (regularizer hH τ).PosSemidef := by
  exact (Matrix.PosSemidef.diagonal (fun i =>
    inv_nonneg.mpr (Real.sqrt_nonneg (hH.eigenvalues i + τ)))).mul_mul_conjTranspose_same
      (hH.eigenvectorUnitary : Matrix ι ι ℝ)

theorem regularizer_transpose (hH : H.IsHermitian) (τ : ℝ) :
    (regularizer hH τ)ᵀ = regularizer hH τ := by
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
    (regularizer_isHermitian hH τ).eq

private theorem regularizer_sqrt_pos (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) (i : ι) : 0 < Real.sqrt (hH.eigenvalues i + τ) := by
  apply Real.sqrt_pos.mpr
  have he : 0 ≤ hH.eigenvalues i := hPSD.eigenvalues_nonneg i
  linarith

theorem regularizer_mul_inverse (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) :
    regularizer hH τ * regularizerInverse hH τ = 1 := by
  rw [regularizer, regularizerInverse, spectralMultiplier_mul]
  have hf : (fun i => (Real.sqrt (hH.eigenvalues i + τ))⁻¹ *
      Real.sqrt (hH.eigenvalues i + τ)) = (fun _ => (1:ℝ)) := by
    ext i
    exact inv_mul_cancel₀ (regularizer_sqrt_pos hH hPSD hτ i).ne'
  rw [hf, spectralMultiplier_one]

theorem regularizer_inverse_mul (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) :
    regularizerInverse hH τ * regularizer hH τ = 1 := by
  rw [regularizerInverse, regularizer, spectralMultiplier_mul]
  have hf : (fun i => Real.sqrt (hH.eigenvalues i + τ) *
      (Real.sqrt (hH.eigenvalues i + τ))⁻¹) = (fun _ => (1:ℝ)) := by
    ext i
    exact mul_inv_cancel₀ (regularizer_sqrt_pos hH hPSD hτ i).ne'
  rw [hf, spectralMultiplier_one]

theorem regularizer_isUnit (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) : IsUnit (regularizer hH τ) :=
  ⟨⟨regularizer hH τ, regularizerInverse hH τ,
    regularizer_mul_inverse hH hPSD hτ, regularizer_inverse_mul hH hPSD hτ⟩, rfl⟩

/-- Exact normalization of the regularized population matrix. -/
theorem regularizer_normalizes (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) :
    regularizer hH τ * (H + τ • (1 : Matrix ι ι ℝ)) * regularizer hH τ = 1 := by
  have hshift : H + τ • (1 : Matrix ι ι ℝ) =
      spectralMultiplier hH (fun i => hH.eigenvalues i + τ) := by
    rw [spectralMultiplier_add, spectralMultiplier_eigenvalues, spectralMultiplier_const]
  rw [hshift, regularizer, spectralMultiplier_mul, spectralMultiplier_mul]
  have hf : (fun i => ((Real.sqrt (hH.eigenvalues i + τ))⁻¹ *
      (hH.eigenvalues i + τ)) * (Real.sqrt (hH.eigenvalues i + τ))⁻¹) =
      (fun _ => (1:ℝ)) := by
    ext i
    have hp := regularizer_sqrt_pos hH hPSD hτ i
    have hs : Real.sqrt (hH.eigenvalues i + τ) * Real.sqrt (hH.eigenvalues i + τ) =
        hH.eigenvalues i + τ := Real.mul_self_sqrt (by
          have he := hPSD.eigenvalues_nonneg i
          linarith)
    calc
      _ = (Real.sqrt (hH.eigenvalues i + τ))⁻¹ *
          (Real.sqrt (hH.eigenvalues i + τ) * Real.sqrt (hH.eigenvalues i + τ)) *
          (Real.sqrt (hH.eigenvalues i + τ))⁻¹ :=
        congrArg (fun z : ℝ => (Real.sqrt (hH.eigenvalues i + τ))⁻¹ * z *
          (Real.sqrt (hH.eigenvalues i + τ))⁻¹) hs.symm
      _ = 1 := by field_simp [hp.ne']
  rw [hf, spectralMultiplier_one]

theorem regularizer_population_posSemidef (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    (τ : ℝ) : (regularizer hH τ * H * regularizer hH τ).PosSemidef := by
  have hp := hPSD.mul_mul_conjTranspose_same (regularizer hH τ)
  rwa [(regularizer_isHermitian hH τ).eq] at hp

/-- Matrix form of the energy identity `AHA + τ A² = I`. -/
theorem regularizer_energy_matrix (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) :
    regularizer hH τ * H * regularizer hH τ +
      τ • (regularizer hH τ * regularizer hH τ) = 1 := by
  simpa only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_one] using regularizer_normalizes hH hPSD hτ

omit [DecidableEq ι] in
private theorem symmetric_square_quadratic (A : Matrix ι ι ℝ) (hA : Aᵀ = A)
    (x : ι → ℝ) : x ⬝ᵥ ((A*A) *ᵥ x) = (A *ᵥ x) ⬝ᵥ (A *ᵥ x) := by
  rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA]

/-- The exact scalar energy decomposition, for every real vector. -/
theorem regularizer_energy_identity (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) (x : ι → ℝ) :
    x ⬝ᵥ ((regularizer hH τ * H * regularizer hH τ) *ᵥ x) +
      τ * ((regularizer hH τ *ᵥ x) ⬝ᵥ (regularizer hH τ *ᵥ x)) = x ⬝ᵥ x := by
  have h := congrArg (fun M : Matrix ι ι ℝ => x ⬝ᵥ (M *ᵥ x))
    (regularizer_energy_matrix hH hPSD hτ)
  simpa only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add, dotProduct_smul,
    smul_eq_mul, Matrix.one_mulVec,
    symmetric_square_quadratic _ (regularizer_transpose hH τ)] using h

/-- `AHA` is positive semidefinite and is a quadratic-form contraction. -/
theorem regularizer_population_quadratic (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) (x : ι → ℝ) :
    0 ≤ x ⬝ᵥ ((regularizer hH τ * H * regularizer hH τ) *ᵥ x) ∧
      x ⬝ᵥ ((regularizer hH τ * H * regularizer hH τ) *ᵥ x) ≤ x ⬝ᵥ x := by
  have hp : 0 ≤ x ⬝ᵥ ((regularizer hH τ * H * regularizer hH τ) *ᵥ x) := by
    simpa using (regularizer_population_posSemidef hH hPSD τ).2 x
  have hn : 0 ≤ (regularizer hH τ *ᵥ x) ⬝ᵥ (regularizer hH τ *ᵥ x) := by
    simpa using dotProduct_star_self_nonneg (regularizer hH τ *ᵥ x)
  have he := regularizer_energy_identity hH hPSD hτ x
  exact ⟨hp, by nlinarith⟩

/-- The requested Euclidean energy bound, in the form used for edge vectors. -/
theorem regularizer_energy_le (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) (x : ι → ℝ) :
    τ * ((regularizer hH τ *ᵥ x) ⬝ᵥ (regularizer hH τ *ᵥ x)) ≤ x ⬝ᵥ x := by
  have hp := (regularizer_population_quadratic hH hPSD hτ x).1
  linarith [regularizer_energy_identity hH hPSD hτ x]

/-- The energy bound written as the ordinary Euclidean sum of squares. -/
theorem regularizer_sum_sq_le (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) (x : ι → ℝ) :
    τ * (∑ i, (regularizer hH τ *ᵥ x) i ^ 2) ≤ ∑ i, x i ^ 2 := by
  simpa only [dotProduct, ← pow_two] using regularizer_energy_le hH hPSD hτ x

/-- Loewner form `AHA ≼ I`. -/
theorem regularizer_population_le_one (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) :
    ((1 : Matrix ι ι ℝ) - regularizer hH τ * H * regularizer hH τ).PosSemidef := by
  refine ⟨Matrix.isHermitian_one.sub (regularizer_population_posSemidef hH hPSD τ).1, ?_⟩
  intro x
  have hh := (regularizer_population_quadratic hH hPSD hτ x).2
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, star_trivial] using
    sub_nonneg.mpr hh

/-- Loewner form `A² ≼ τ⁻¹ I`. -/
theorem regularizer_square_le_inv (hH : H.IsHermitian) (hPSD : H.PosSemidef)
    {τ : ℝ} (hτ : 0 < τ) :
    (τ⁻¹ • (1 : Matrix ι ι ℝ) - regularizer hH τ * regularizer hH τ).PosSemidef := by
  have hA := regularizer_isHermitian hH τ
  have hAA : (regularizer hH τ * regularizer hH τ).IsHermitian := by
    simpa only [pow_two] using hA.pow 2
  have hI : (τ⁻¹ • (1 : Matrix ι ι ℝ)).IsHermitian := by
    rw [← spectralMultiplier_const hH τ⁻¹]
    exact spectralMultiplier_isHermitian hH _
  refine ⟨hI.sub hAA, ?_⟩
  intro x
  have he := regularizer_energy_le hH hPSD hτ x
  have hle : (regularizer hH τ *ᵥ x) ⬝ᵥ (regularizer hH τ *ᵥ x) ≤
      τ⁻¹ * (x ⬝ᵥ x) := by
    rw [← div_eq_inv_mul]
    apply (le_div_iff₀ hτ).mpr
    nlinarith
  simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul, Matrix.one_mulVec, star_trivial,
    symmetric_square_quadratic _ (regularizer_transpose hH τ)] using sub_nonneg.mpr hle

end Regularizer
end PsgEst
