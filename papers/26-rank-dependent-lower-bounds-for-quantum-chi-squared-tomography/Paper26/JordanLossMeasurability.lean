import Paper26.LossMeasurability
import Mathlib.LinearAlgebra.Matrix.Vec

/-! Actual vectorized Jordan operators and joint Bures-loss measurability.
All matrix spaces have canonical complex-entry sigma-algebras. -/
noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal Topology
open MeasureTheory Paper26.QuantumModel Paper26.ContinuousPOVM Matrix Kronecker

namespace Paper26.JordanLossMeasurability
open SupportCompression

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The actual coefficient matrix of `X ↦ (AX+XA)/2`, in column-vector coordinates. -/
def jordanMatrix (A : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  (1 / 2 : ℂ) • ((1 : Matrix ι ι ℂ) ⊗ₖ A + Aᵀ ⊗ₖ (1 : Matrix ι ι ℂ))

/-- Actual coordinate matrix for unitary conjugation on matrices. -/
def conjugationMatrix (U : Matrix ι ι ℂ) : Matrix (ι × ι) (ι × ι) ℂ :=
  U.map (starRingEnd ℂ) ⊗ₖ U

omit [DecidableEq ι] in
theorem conjugationMatrix_action (U X : Matrix ι ι ℂ) :
    conjugationMatrix U *ᵥ Matrix.vec X = Matrix.vec (Normalization.conjugate U X) := by
  rw [conjugationMatrix, Matrix.kronecker_mulVec_vec]
  rfl

omit [Fintype ι] [DecidableEq ι] in
theorem conjugationMatrix_adjoint (U : Matrix ι ι ℂ) :
    (conjugationMatrix U)ᴴ = conjugationMatrix Uᴴ := by
  ext p q
  simp [conjugationMatrix, Matrix.conjTranspose_apply, StarMul.star_mul, mul_comm]

omit [DecidableEq ι] in
theorem conjugationMatrix_mul (U V : Matrix ι ι ℂ) :
    conjugationMatrix U * conjugationMatrix V = conjugationMatrix (U * V) := by
  rw [conjugationMatrix, conjugationMatrix, ← Matrix.mul_kronecker_mul,
    ← Matrix.map_mul]
  rfl

omit [Fintype ι] in
@[simp] theorem conjugationMatrix_one : conjugationMatrix (1 : Matrix ι ι ℂ) = 1 := by
  simp [conjugationMatrix]

def conjugationUnitary (U : Matrix.unitaryGroup ι ℂ) : Matrix.unitaryGroup (ι × ι) ℂ :=
  ⟨conjugationMatrix (U : Matrix ι ι ℂ), by
    constructor
    · change (conjugationMatrix (U : Matrix ι ι ℂ))ᴴ * conjugationMatrix (U : Matrix ι ι ℂ) = 1
      rw [conjugationMatrix_adjoint, conjugationMatrix_mul,
        PositiveLossBridge.unitary_left U, conjugationMatrix_one]
    · change conjugationMatrix (U : Matrix ι ι ℂ) * (conjugationMatrix (U : Matrix ι ι ℂ))ᴴ = 1
      rw [conjugationMatrix_adjoint, conjugationMatrix_mul,
        PositiveLossBridge.unitary_right U, conjugationMatrix_one]⟩

theorem jordanMatrix_action (A X : Matrix ι ι ℂ) :
    jordanMatrix A *ᵥ Matrix.vec X = Matrix.vec ((1 / 2 : ℂ) • (A * X + X * A)) := by
  rw [jordanMatrix, Matrix.smul_mulVec, Matrix.add_mulVec,
    Matrix.kronecker_mulVec_vec, Matrix.kronecker_mulVec_vec,
    Matrix.transpose_one, Matrix.transpose_transpose, Matrix.mul_one, Matrix.one_mul,
    ← Matrix.vec_add, ← Matrix.vec_smul]

lemma matrix_eq_of_vec_action {M N : Matrix (ι × ι) (ι × ι) ℂ}
    (h : ∀ X : Matrix ι ι ℂ, M *ᵥ Matrix.vec X = N *ᵥ Matrix.vec X) : M = N := by
  apply Matrix.ext_of_mulVec_single
  intro j
  obtain ⟨X, hX⟩ := (Matrix.vec_bijective (m := ι) (n := ι) (R := ℂ)).surjective (Pi.single j 1)
  rw [← hX]
  exact h X

/-- Native transport of the actual Jordan coefficient matrix. -/
theorem jordanMatrix_conjugate (U : Matrix.unitaryGroup ι ℂ) (A : Matrix ι ι ℂ) :
    jordanMatrix (Normalization.conjugate (U : Matrix ι ι ℂ) A) =
      Normalization.conjugate (conjugationUnitary U : Matrix (ι × ι) (ι × ι) ℂ)
        (jordanMatrix A) := by
  apply matrix_eq_of_vec_action
  intro X
  change jordanMatrix _ *ᵥ Matrix.vec X =
    (conjugationMatrix (U : Matrix ι ι ℂ) * jordanMatrix A *
      (conjugationMatrix (U : Matrix ι ι ℂ))ᴴ) *ᵥ Matrix.vec X
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    conjugationMatrix_adjoint, conjugationMatrix_action, jordanMatrix_action,
    jordanMatrix_action, conjugationMatrix_action]
  apply congrArg Matrix.vec
  have hback : Normalization.conjugate (U : Matrix ι ι ℂ)ᴴ X =
      Normalization.coordinates (U : Matrix ι ι ℂ) X := by
    simp [Normalization.conjugate, Normalization.coordinates]
  rw [hback]
  change _ = Normalization.conjugate (U : Matrix ι ι ℂ)
    ((1 / 2 : ℂ) • (A * Normalization.coordinates (U : Matrix ι ι ℂ) X +
      Normalization.coordinates (U : Matrix ι ι ℂ) X * A))
  rw [Normalization.conjugate_smul, Normalization.conjugate_add,
    Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
    Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left U),
    Normalization.conjugate_coordinates _ _ (PositiveLossBridge.unitary_right U)]

def jordanSpectrum (a : ι → ℝ) (p : ι × ι) : ℝ := (a p.2 + a p.1) / 2

omit [Fintype ι] in
theorem jordanMatrix_diagonal (a : ι → ℝ) :
    jordanMatrix (Normalization.diagonalMatrix a) =
      Normalization.diagonalMatrix (jordanSpectrum a) := by
  ext ⟨j, i⟩ ⟨l, k⟩
  by_cases h₁ : j = l <;> by_cases h₂ : i = k
  all_goals
    simp [jordanMatrix, Normalization.diagonalMatrix, jordanSpectrum, h₁, h₂, Prod.ext_iff]
  subst l
  subst k
  ring

/-- Actual Jordan spectral bridge, valid for every density including singular outputs. -/
theorem jordanMatrix_spectral (σ : Density ι) :
    jordanMatrix σ.matrix =
      Normalization.conjugate (conjugationUnitary σ.eigenbasis : Matrix (ι × ι) (ι × ι) ℂ)
        (Normalization.diagonalMatrix (jordanSpectrum σ.spectrum)) := by
  rw [PositiveLossBridge.density_spectral_reconstruction σ, jordanMatrix_conjugate,
    jordanMatrix_diagonal]

theorem jordanMatrix_posSemidef (σ : Density ι) : (jordanMatrix σ.matrix).PosSemidef := by
  rw [jordanMatrix_spectral]
  apply Matrix.PosSemidef.mul_mul_conjTranspose_same
  apply Matrix.PosSemidef.diagonal
  intro p
  exact RCLike.ofReal_nonneg.mpr (div_nonneg
    (add_nonneg (σ.spectrum_nonneg p.2) (σ.spectrum_nonneg p.1)) (by norm_num))

theorem jordanMatrix_trace (σ : Density ι) :
    Matrix.trace (jordanMatrix σ.matrix) = (Fintype.card ι : ℂ) := by
  simp [jordanMatrix, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_kronecker,
    σ.trace_one, Matrix.trace_transpose]
  ring

section Nonempty
variable [Nonempty ι]

/-- The actual Jordan operator normalized to an actual density matrix. -/
def jordanDensity (σ : Density ι) : Density (ι × ι) where
  matrix := ((Fintype.card ι : ℝ)⁻¹) • jordanMatrix σ.matrix
  positive := (jordanMatrix_posSemidef σ).smul (by positivity)
  trace_one := by
    rw [Matrix.trace_smul, jordanMatrix_trace]
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp [Complex.real_smul, ← Complex.ofReal_natCast, hn]

omit [Fintype ι] [Nonempty ι] in
lemma diagonal_real_smul (c : ℝ) (a : ι → ℝ) :
    Normalization.diagonalMatrix (fun i => c * a i) = c • Normalization.diagonalMatrix a := by
  ext i j
  by_cases hij : i = j <;> simp [Normalization.diagonalMatrix, hij, Complex.real_smul]

omit [Nonempty ι] in
lemma conjugate_real_smul (U X : Matrix ι ι ℂ) (c : ℝ) :
    Normalization.conjugate U (c • X) = c • Normalization.conjugate U X := by
  simp [Normalization.conjugate]

theorem jordanDensity_spectral (σ : Density ι) :
    (jordanDensity σ).matrix =
      Normalization.conjugate (conjugationUnitary σ.eigenbasis : Matrix (ι × ι) (ι × ι) ℂ)
        (Normalization.diagonalMatrix (fun p =>
          (Fintype.card ι : ℝ)⁻¹ * jordanSpectrum σ.spectrum p)) := by
  rw [diagonal_real_smul, conjugate_real_smul, ← jordanMatrix_spectral]
  rfl

/-- Intrinsic Moore–Penrose inverse of the actual Jordan matrix. -/
def pseudoJordan (σ : Density ι) : Matrix (ι × ι) (ι × ι) ℂ :=
  ((Fintype.card ι : ℝ)⁻¹) • pinv (jordanDensity σ)

theorem pseudoJordan_spectral (σ : Density ι) :
    pseudoJordan σ =
      Normalization.conjugate (conjugationUnitary σ.eigenbasis : Matrix (ι × ι) (ι × ι) ℂ)
        (Normalization.diagonalMatrix (fun p => (jordanSpectrum σ.spectrum p)⁻¹)) := by
  let a := fun p => (Fintype.card ι : ℝ)⁻¹ * jordanSpectrum σ.spectrum p
  have hInv : HermitianInverse (jordanDensity σ).matrix
      (Normalization.conjugate (conjugationUnitary σ.eigenbasis : Matrix (ι × ι) (ι × ι) ℂ)
        (Normalization.diagonalMatrix (fun p => (a p)⁻¹))) := by
    rw [jordanDensity_spectral]
    exact (diagonal_inverse_properties a).conjugate (conjugationUnitary σ.eigenbasis)
  have hp := (pinv_properties (jordanDensity σ)).unique (jordanDensity σ).hermitian hInv
  unfold pseudoJordan
  rw [hp, ← conjugate_real_smul, ← diagonal_real_smul]
  congr 2
  funext p
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [a, _root_.mul_inv_rev, inv_inv]
  field_simp

theorem pseudoJordan_properties (σ : Density ι) :
    HermitianInverse (jordanMatrix σ.matrix) (pseudoJordan σ) := by
  rw [jordanMatrix_spectral, pseudoJordan_spectral]
  exact (diagonal_inverse_properties (jordanSpectrum σ.spectrum)).conjugate
    (conjugationUnitary σ.eigenbasis)

/-- Actual vectorized quadratic energy of the Moore–Penrose Jordan inverse. -/
def buresEnergy (ρ σ : Density ι) : ℝ :=
  (star (Matrix.vec (ρ.matrix - σ.matrix)) ⬝ᵥ
    (pseudoJordan σ *ᵥ Matrix.vec (ρ.matrix - σ.matrix))).re

omit [Nonempty ι] in
lemma quadratic_conjugate (U : Matrix.unitaryGroup ι ℂ) (D : Matrix ι ι ℂ) (v : ι → ℂ) :
    star v ⬝ᵥ (Normalization.conjugate (U : Matrix ι ι ℂ) D *ᵥ v) =
      star ((U : Matrix ι ι ℂ)ᴴ *ᵥ v) ⬝ᵥ (D *ᵥ ((U : Matrix ι ι ℂ)ᴴ *ᵥ v)) := by
  rw [Normalization.conjugate, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]

theorem buresEnergy_spectral (ρ σ : Density ι) :
    buresEnergy ρ σ = SpectralLoss.bures σ.spectrum (eigenDifference ρ σ) := by
  have hcoord : (conjugationUnitary σ.eigenbasis : Matrix (ι × ι) (ι × ι) ℂ)ᴴ *ᵥ
      Matrix.vec (ρ.matrix - σ.matrix) = Matrix.vec (eigenDifference ρ σ) := by
    change (conjugationMatrix (σ.eigenbasis : Matrix ι ι ℂ))ᴴ *ᵥ _ = _
    rw [conjugationMatrix_adjoint, conjugationMatrix_action]
    simp only [Normalization.conjugate, Matrix.conjTranspose_conjTranspose,
      eigenDifference, Matrix.star_eq_conjTranspose]
  rw [buresEnergy, pseudoJordan_spectral, quadratic_conjugate, hcoord]
  simp only [Normalization.diagonalMatrix, Matrix.mulVec_diagonal, dotProduct,
    Fintype.sum_prod_type, Complex.re_sum, Pi.star_apply, Matrix.vec,
    jordanSpectrum]
  rw [Finset.sum_comm]
  unfold SpectralLoss.bures
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  let z := eigenDifference ρ σ i j
  let w : ℝ := (σ.spectrum i + σ.spectrum j) / 2
  change (star z * (((w⁻¹ : ℝ) : ℂ) * z)).re = 2 * Complex.normSq z / (σ.spectrum i + σ.spectrum j)
  calc
    _ = w⁻¹ * Complex.normSq z := by
      have he : star z * (((w⁻¹ : ℝ) : ℂ) * z) = ((w⁻¹ : ℝ) : ℂ) * (Complex.normSq z : ℂ) := by
        rw [Complex.normSq_eq_conj_mul_self]
        simp only [Complex.star_def]
        ring
      rw [he, ← Complex.ofReal_mul, Complex.ofReal_re]
    _ = _ := by
      simp only [w, div_eq_mul_inv, _root_.mul_inv_rev, inv_inv]
      ring

omit [Nonempty ι] in
theorem bures_support_eq (ρ σ : Density ι) (h : SupportContained ρ σ) :
    SpectralLoss.bures (supportSpectrum σ) (supportDifference ρ σ) =
      SpectralLoss.bures σ.spectrum (eigenDifference ρ σ) := by
  unfold SpectralLoss.bures supportSpectrum supportDifference
  simp only [Matrix.submatrix_apply]
  calc
    _ = ∑ i, ∑ j : SupportIndex σ,
        2 * Complex.normSq (eigenDifference ρ σ i j.val) / (σ.spectrum i + σ.spectrum j.val) := by
      apply sum_support_eq σ (fun i => ∑ j : SupportIndex σ,
        2 * Complex.normSq (eigenDifference ρ σ i j.val) / (σ.spectrum i + σ.spectrum j.val))
      intro i hi
      have hz : σ.spectrum i = 0 := le_antisymm (le_of_not_gt hi) (σ.spectrum_nonneg i)
      apply Finset.sum_eq_zero
      intro j _
      simp [eigenDifference_zero_row ρ σ h i hz j.val]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      apply sum_support_eq σ (fun j =>
        2 * Complex.normSq (eigenDifference ρ σ i j) / (σ.spectrum i + σ.spectrum j))
      intro j hj
      have hz : σ.spectrum j = 0 := le_antisymm (le_of_not_gt hj) (σ.spectrum_nonneg j)
      simp [eigenDifference_zero_column ρ σ h j hz i]

/-- Intrinsic Bures energy bridge with the actual support convention. -/
theorem chiB_eq_jordan_energy (ρ σ : Density ι) (h : SupportContained ρ σ) :
    chiB ρ σ = ENNReal.ofReal (buresEnergy ρ σ) := by
  rw [chiB, if_pos h, bures_support_eq ρ σ h, buresEnergy_spectral]

omit [Fintype ι] [Nonempty ι] in
/-- The actual Jordan coefficient matrix is polynomial in the actual entries. -/
theorem continuous_jordanMatrix : Continuous (jordanMatrix : Matrix ι ι ℂ → Matrix (ι × ι) (ι × ι) ℂ) := by
  apply continuous_matrix
  intro p q
  simp only [jordanMatrix, Matrix.smul_apply, Matrix.add_apply, Matrix.kroneckerMap_apply,
    Matrix.transpose_apply, smul_eq_mul]
  exact continuous_const.mul ((continuous_const.mul (continuous_apply_apply p.2 q.2)).add
    ((continuous_apply_apply q.1 p.1).mul continuous_const))

theorem measurable_jordanDensity : Measurable (jordanDensity : Density ι → Density (ι × ι)) := by
  apply LossMeasurability.measurable_density_of_matrix
  have hJ : Measurable (fun σ : Density ι => jordanMatrix σ.matrix) :=
    continuous_jordanMatrix.measurable.comp measurable_density_matrix
  apply measurable_pi_iff.2
  intro p
  apply measurable_pi_iff.2
  intro q
  exact ((measurable_pi_apply q).comp ((measurable_pi_apply p).comp hJ)).const_smul ((Fintype.card ι : ℝ)⁻¹)

theorem measurable_pseudoJordan : Measurable (pseudoJordan : Density ι → Matrix (ι × ι) (ι × ι) ℂ) := by
  have hp : Measurable (fun σ : Density ι => pinv (jordanDensity σ)) :=
    LossMeasurability.measurable_pinv.comp measurable_jordanDensity
  apply measurable_pi_iff.2
  intro p
  apply measurable_pi_iff.2
  intro q
  exact ((measurable_pi_apply q).comp ((measurable_pi_apply p).comp hp)).const_smul ((Fintype.card ι : ℝ)⁻¹)

theorem measurable_buresEnergy : Measurable (fun p : Density ι × Density ι => buresEnergy p.1 p.2) := by
  have hD (p : ι × ι) : Measurable (fun x : Density ι × Density ι =>
      Matrix.vec (x.1.matrix - x.2.matrix) p) :=
    (((measurable_pi_apply p.1).comp ((measurable_pi_apply p.2).comp measurable_density_matrix)).comp
      measurable_fst).sub
    (((measurable_pi_apply p.1).comp ((measurable_pi_apply p.2).comp measurable_density_matrix)).comp
      measurable_snd)
  have hJ (p q : ι × ι) : Measurable (fun x : Density ι × Density ι => pseudoJordan x.2 p q) :=
    ((measurable_pi_apply q).comp ((measurable_pi_apply p).comp measurable_pseudoJordan)).comp measurable_snd
  apply Complex.continuous_re.measurable.comp
  exact Finset.measurable_sum Finset.univ fun p _ =>
    (Complex.continuous_conj.measurable.comp (hD p)).mul
      (Finset.measurable_sum Finset.univ fun q _ => (hJ p q).mul (hD q))

theorem measurable_chiB_nonempty : Measurable (fun p : Density ι × Density ι => chiB p.1 p.2) := by
  classical
  have heq : (fun p : Density ι × Density ι => chiB p.1 p.2) =
      (fun p => if SupportContained p.1 p.2 then ENNReal.ofReal (buresEnergy p.1 p.2) else ∞) := by
    funext p
    split_ifs with h
    · exact chiB_eq_jordan_energy p.1 p.2 h
    · exact chiB_eq_top_of_not_supportContained p.1 p.2 h
  rw [heq]
  exact Measurable.ite LossMeasurability.measurableSet_supportContained
    (ENNReal.measurable_ofReal.comp measurable_buresEnergy) measurable_const

end Nonempty

/-- Full joint measurability of actual Bures chi-squared loss. The empty
ambient index case is vacuous, since a trace-one density then cannot exist. -/
theorem measurable_chiB : Measurable (fun p : Density ι × Density ι => chiB p.1 p.2) := by
  classical
  by_cases hι : Nonempty ι
  · letI := hι
    exact measurable_chiB_nonempty
  · letI : IsEmpty ι := not_nonempty_iff.mp hι
    haveI : IsEmpty (Density ι) := ⟨fun ρ => by simpa [Matrix.trace] using ρ.trace_one⟩
    exact measurable_of_empty _

section SuccessEvents
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

theorem measurable_chiB_comp (f g : α → Density ι) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => chiB (f x) (g x)) := by
  intro S hS
  exact (hf.prodMk hg) ((measurable_chiB (ι := ι)) hS)

theorem measurable_joint_chiB (f : α → Density ι) (g : β → Density ι)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z : α × β => chiB (f z.1) (g z.2)) :=
  measurable_chiB_comp _ _ (hf.comp measurable_fst) (hg.comp measurable_snd)

theorem measurableSet_joint_estimator_success (f : α → Density ι) (hf : Measurable f)
    (T : Estimator ι β) (ε : ℝ≥0∞) :
    MeasurableSet {z : α × β | chiB (f z.1) (T.estimate z.2) ≤ ε} :=
  measurableSet_le (measurable_joint_chiB f T.estimate hf T.measurable_estimate) measurable_const

end SuccessEvents

theorem measurableSet_frame_estimator_success {κ Y : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] [MeasurableSpace Y]
    (T : Estimator ι Y) (ε : ℝ≥0∞) :
    MeasurableSet {z : HaarFrames.Frame ι κ × Y | chiB z.1.density (T.estimate z.2) ≤ ε} :=
  measurableSet_joint_estimator_success _ LossMeasurability.measurable_frame_density T ε

theorem measurableSet_graph_estimator_success {κ σ Y : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype σ] [DecidableEq σ] [MeasurableSpace Y]
    (T : Estimator (κ ⊕ σ) Y) (ε : ℝ≥0∞) :
    MeasurableSet {z : Matrix σ κ ℂ × Y |
      chiB (GraphFamily.density z.1) (T.estimate z.2) ≤ ε} :=
  measurableSet_joint_estimator_success _ GraphFamily.measurable_density T ε
end Paper26.JordanLossMeasurability
