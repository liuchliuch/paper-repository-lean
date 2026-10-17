import Paper26.SupportCompression
import Paper26.HaarFrames
import Paper26.GraphFamily
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Joint measurability of actual right-inverse chi-squared loss

The Moore–Penrose inverse is the entrywise limit of rational regularizations
`σ (σ² + η I)⁻¹`, with `η → 0+`. Each regularization is measurable in the actual
matrix entries. Spectral coordinates are used only at a fixed matrix to prove
convergence, never as a measurable eigenbasis-selection hypothesis.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal Topology
open MeasureTheory Filter Paper26.QuantumModel Paper26.ContinuousPOVM

namespace Paper26.LossMeasurability

open SupportCompression

local instance matrixMeasurableSpace (m n : Type*) : MeasurableSpace (Matrix m n ℂ) :=
  inferInstanceAs (MeasurableSpace (m → n → ℂ))
local instance matrixBorelSpace (m n : Type*) [Fintype m] [Fintype n] :
    BorelSpace (Matrix m n ℂ) := inferInstanceAs (BorelSpace (m → n → ℂ))

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Rational matrix regularization, with the actual nonsingular inverse. -/
def regularization (η : ℝ) (A : Matrix ι ι ℂ) : Matrix ι ι ℂ :=
  A * (A * A + (η : ℂ) • (1 : Matrix ι ι ℂ))⁻¹

def eta (m : ℕ) : ℝ := 1 / ((m : ℝ) + 1)

theorem eta_pos (m : ℕ) : 0 < eta m := by unfold eta; positivity

theorem tendsto_eta : Tendsto eta atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat

/-- Scalar convergence includes zero eigenvalues exactly. -/
theorem tendsto_scalar (t : ℝ) :
    Tendsto (fun m => t / (t ^ 2 + eta m)) atTop (𝓝 (t⁻¹)) := by
  by_cases ht : t = 0
  · simp only [ht, zero_div, inv_zero]
    exact tendsto_const_nhds
  · have h : Tendsto (fun m => t / (t ^ 2 + eta m)) atTop (𝓝 (t / (t ^ 2 + 0))) :=
      tendsto_const_nhds.div (tendsto_const_nhds.add tendsto_eta)
        (show t ^ 2 + 0 ≠ 0 by simpa only [add_zero] using pow_ne_zero 2 ht)
    have he : t / (t ^ 2 + 0) = t⁻¹ := by rw [add_zero]; field_simp
    simpa only [he] using h

lemma diagonal_square_shift (a : ι → ℝ) (η : ℝ) :
    Normalization.diagonalMatrix (fun i => a i ^ 2 + η) =
      Normalization.diagonalMatrix a * Normalization.diagonalMatrix a +
        (η : ℂ) • (1 : Matrix ι ι ℂ) := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Normalization.diagonalMatrix, Matrix.diagonal_mul_diagonal, pow_two]
  · simp [Normalization.diagonalMatrix, Matrix.diagonal_mul_diagonal, hij]

lemma conjugate_scalar_identity (U : Matrix.unitaryGroup ι ℂ) (η : ℝ) :
    Normalization.conjugate (U : Matrix ι ι ℂ) ((η : ℂ) • (1 : Matrix ι ι ℂ)) =
      (η : ℂ) • (1 : Matrix ι ι ℂ) := by
  rw [Normalization.conjugate_smul]
  simp only [Normalization.conjugate, Matrix.mul_one, PositiveLossBridge.unitary_right U]

/-- An algebraic spectral formula for a fixed output; no joint regularity
of its selected eigenvectors is used or asserted. -/
theorem regularization_spectral (σ : Density ι) (η : ℝ) (hη : 0 < η) :
    regularization η σ.matrix = Normalization.conjugate (σ.eigenbasis : Matrix ι ι ℂ)
      (Normalization.diagonalMatrix (fun i => σ.spectrum i / (σ.spectrum i ^ 2 + η))) := by
  have hd : σ.matrix * σ.matrix + (η : ℂ) • (1 : Matrix ι ι ℂ) =
      Normalization.conjugate (σ.eigenbasis : Matrix ι ι ℂ)
        (Normalization.diagonalMatrix (fun i => σ.spectrum i ^ 2 + η)) := by
    rw [diagonal_square_shift, Normalization.conjugate_add,
      Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left σ.eigenbasis),
      conjugate_scalar_identity, ← PositiveLossBridge.density_spectral_reconstruction σ]
  rw [regularization, hd, Normalization.conjugate_diagonal_inverse _ _
    (PositiveLossBridge.unitary_left σ.eigenbasis)
    (PositiveLossBridge.unitary_right σ.eigenbasis) (fun i => by positivity),
    PositiveLossBridge.density_spectral_reconstruction σ,
    ← Normalization.conjugate_mul _ _ _ (PositiveLossBridge.unitary_left σ.eigenbasis)]
  congr 1
  ext i j
  by_cases hij : i = j
  · subst j
    simp [Normalization.diagonalMatrix, div_eq_mul_inv]
  · simp [Normalization.diagonalMatrix, hij]

lemma conjugate_diagonal_entry (U : Matrix ι ι ℂ) (a : ι → ℝ) (i j : ι) :
    Normalization.conjugate U (Normalization.diagonalMatrix a) i j =
      ∑ k, U i k * (a k : ℂ) * star (U j k) := by
  simp [Normalization.conjugate, Normalization.diagonalMatrix, Matrix.mul_apply,
    Matrix.diagonal_apply]

/-- Entrywise convergence of actual rational matrices to the actual
Moore–Penrose inverse, including singular outputs. -/
theorem tendsto_regularization_entry (σ : Density ι) (i j : ι) :
    Tendsto (fun m => regularization (eta m) σ.matrix i j) atTop (𝓝 (pinv σ i j)) := by
  simp_rw [regularization_spectral σ _ (eta_pos _)]
  simp only [pinv, conjugate_diagonal_entry]
  apply tendsto_finset_sum
  intro k _
  have h := Complex.continuous_ofReal.tendsto (σ.spectrum k)⁻¹ |>.comp (tendsto_scalar (σ.spectrum k))
  exact (tendsto_const_nhds.mul h).mul_const _

omit [DecidableEq ι] in
/-- Finite matrix multiplication preserves canonical entrywise measurability. -/
lemma measurable_matrix_mul {α : Type*} [MeasurableSpace α]
    (f g : α → Matrix ι ι ℂ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x * g x) := by
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  exact Finset.measurable_sum Finset.univ fun k _ =>
    ((measurable_pi_apply k).comp ((measurable_pi_apply i).comp hf)).mul
      ((measurable_pi_apply j).comp ((measurable_pi_apply k).comp hg))

omit [Fintype ι] [DecidableEq ι] in
lemma measurable_matrix_sub {α : Type*} [MeasurableSpace α]
    (f g : α → Matrix ι ι ℂ) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => f x - g x) := by
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hf)).sub
    ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hg))

/-- The totalized actual matrix inverse is measurable; invertibility is not
needed because the adjugate formula uses the measurable scalar inverse. -/
theorem measurable_matrix_inverse : Measurable (fun A : Matrix ι ι ℂ => A⁻¹) := by
  have hd : Measurable (fun A : Matrix ι ι ℂ => A.det) := continuous_id.matrix_det.measurable
  have ha : Measurable (fun A : Matrix ι ι ℂ => A.adjugate) := continuous_id.matrix_adjugate.measurable
  simpa only [Matrix.inv_def, Ring.inverse_eq_inv] using hd.inv.smul ha

theorem measurable_regularization (η : ℝ) :
    Measurable (regularization (ι := ι) η) := by
  have hc : Continuous (fun A : Matrix ι ι ℂ => A * A + (η : ℂ) • (1 : Matrix ι ι ℂ)) :=
    (continuous_id.matrix_mul continuous_id).add continuous_const
  exact measurable_matrix_mul _ _ measurable_id (measurable_matrix_inverse.comp hc.measurable)

/-- Measurable intrinsic pseudoinverse, obtained as a pointwise limit without
any measurable eigenvector choice. -/
theorem measurable_pinv : Measurable (pinv : Density ι → Matrix ι ι ℂ) := by
  apply measurable_pi_iff.2
  intro i
  apply measurable_pi_iff.2
  intro j
  apply measurable_of_tendsto_metrizable (fun m =>
    (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      ((measurable_regularization (eta m)).comp measurable_density_matrix)))
  exact tendsto_pi_nhds.2 fun σ => tendsto_regularization_entry σ i j

/-- Joint actual support inclusion is Borel in the canonical density
coordinates, including all singular-output strata. -/
theorem measurableSet_supportContained :
    MeasurableSet {p : Density ι × Density ι | SupportContained p.1 p.2} := by
  have hρ : Measurable (fun p : Density ι × Density ι => p.1.matrix) :=
    measurable_density_matrix.comp measurable_fst
  have hσ : Measurable (fun p : Density ι × Density ι => p.2.matrix) :=
    measurable_density_matrix.comp measurable_snd
  have hP : Measurable (fun p : Density ι × Density ι => pinv p.2) :=
    measurable_pinv.comp measurable_snd
  have htest : Measurable (fun p : Density ι × Density ι =>
      p.1.matrix * (1 - pinv p.2 * p.2.matrix)) :=
    measurable_matrix_mul _ _ hρ (measurable_matrix_sub _ _ measurable_const (measurable_matrix_mul _ _ hP hσ))
  have heq : {p : Density ι × Density ι | SupportContained p.1 p.2} =
      {p | p.1.matrix * (1 - pinv p.2 * p.2.matrix) = 0} := by
    ext p
    exact kernelContained_iff_projection p.1.matrix p.2
  rw [heq]
  exact htest (measurableSet_singleton (0 : Matrix ι ι ℂ))

theorem measurable_rightEnergy : Measurable (fun p : Density ι × Density ι => rightEnergy p.1 p.2) := by
  have hD : Measurable (fun p : Density ι × Density ι => p.1.matrix - p.2.matrix) :=
    measurable_matrix_sub _ _ (measurable_density_matrix.comp measurable_fst)
      (measurable_density_matrix.comp measurable_snd)
  have hM := measurable_matrix_mul _ _ (measurable_matrix_mul _ _ hD hD)
    (measurable_pinv.comp measurable_snd)
  exact Complex.continuous_re.measurable.comp (continuous_id.matrix_trace.measurable.comp hM)

/-- Full joint measurability of actual right-inverse chi-squared loss with
its genuine support/infinity convention. -/
theorem measurable_chiR : Measurable (fun p : Density ι × Density ι => chiR p.1 p.2) := by
  classical
  have heq : (fun p : Density ι × Density ι => chiR p.1 p.2) =
      (fun p => if SupportContained p.1 p.2 then ENNReal.ofReal (rightEnergy p.1 p.2) else ∞) := by
    funext p
    split_ifs with h
    · exact chiR_eq_pinv_trace p.1 p.2 h
    · exact chiR_eq_top_of_not_supportContained p.1 p.2 h
  rw [heq]
  exact Measurable.ite measurableSet_supportContained
    (ENNReal.measurable_ofReal.comp measurable_rightEnergy) measurable_const

section SuccessEvents
variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]

/-- Composition of the full actual loss with any two measurable state maps. -/
theorem measurable_chiR_comp (f g : α → Density ι) (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun x => chiR (f x) (g x)) := by
  intro S hS
  exact (hf.prodMk hg) ((measurable_chiR (ι := ι)) hS)

theorem measurable_joint_chiR (f : α → Density ι) (g : β → Density ι)
    (hf : Measurable f) (hg : Measurable g) :
    Measurable (fun z : α × β => chiR (f z.1) (g z.2)) :=
  measurable_chiR_comp _ _ (hf.comp measurable_fst) (hg.comp measurable_snd)

theorem measurableSet_chiR_success (f g : α → Density ι)
    (hf : Measurable f) (hg : Measurable g) (ε : ℝ≥0∞) :
    MeasurableSet {x | chiR (f x) (g x) ≤ ε} :=
  measurableSet_le (measurable_chiR_comp f g hf hg) measurable_const

/-- Joint success for an actual input state family and an unrestricted
measurable density-matrix estimator. -/
theorem measurableSet_joint_estimator_success (f : α → Density ι) (hf : Measurable f)
    (T : Estimator ι β) (ε : ℝ≥0∞) :
    MeasurableSet {z : α × β | chiR (f z.1) (T.estimate z.2) ≤ ε} :=
  measurableSet_le (measurable_joint_chiR f T.estimate hf T.measurable_estimate) measurable_const

omit [DecidableEq ι] in
/-- The canonical density sigma-algebra is induced by actual matrix entries. -/
theorem measurable_density_of_matrix (f : α → Density ι)
    (hf : Measurable (fun x => ((f x).matrix : ι → ι → ℂ))) : Measurable f := by
  intro S hS
  rcases hS with ⟨S, hS, rfl⟩
  exact hf hS

end SuccessEvents

/-- Actual flat frame states are measurable as density-matrix-valued maps. -/
theorem measurable_frame_density {κ : Type*} [Fintype κ] [DecidableEq κ] [Nonempty κ] :
    Measurable (fun U : HaarFrames.Frame ι κ => U.density) :=
  measurable_density_of_matrix _ HaarFrames.Frame.measurable_density_matrix

/-- Joint frame/estimator success events, with singular estimator outputs
and the actual infinity convention included. -/
theorem measurableSet_frame_estimator_success {κ Y : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] [MeasurableSpace Y]
    (T : Estimator ι Y) (ε : ℝ≥0∞) :
    MeasurableSet {z : HaarFrames.Frame ι κ × Y | chiR z.1.density (T.estimate z.2) ≤ ε} :=
  measurableSet_joint_estimator_success _ measurable_frame_density T ε

/-- Joint graph-family/estimator success is measurable in the actual
complex matrix coordinates. -/
theorem measurableSet_graph_estimator_success {κ σ Y : Type*}
    [Fintype κ] [DecidableEq κ] [Nonempty κ] [Fintype σ] [DecidableEq σ] [MeasurableSpace Y]
    (T : Estimator (κ ⊕ σ) Y) (ε : ℝ≥0∞) :
    MeasurableSet {z : Matrix σ κ ℂ × Y |
      chiR (GraphFamily.density z.1) (T.estimate z.2) ≤ ε} :=
  measurableSet_joint_estimator_success _ GraphFamily.measurable_density T ε

end Paper26.LossMeasurability
