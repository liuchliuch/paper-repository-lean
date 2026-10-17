import Paper26.CollectiveModel
import Paper26.MatrixCoordinates
import Paper26.WeakPosteriorIdentity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Calculus.FDeriv.Pow
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Actual graph-family experiments in real Euclidean coordinates

A learner is applied to the actual graph density at the inverse of the
`MatrixCoordinates.coordinates` equivalence. Its likelihood is the actual
Born trace of the tensor-copy input and its square root is the real square
root of that likelihood. All outcome spaces are arbitrary measurable spaces;
the reference measure is the learner's finite dominated POVM measure.

This module proves normalization, joint measurability and actual Bayes
normalization from those matrix objects. It separates the analytic derivative
regularity needed by `WeakPosteriorIdentity` from these elementary probability
facts; no posterior-information conclusion is supplied as an external field.
-/

noncomputable section
open scoped BigOperators ENNReal ComplexOrder
open MeasureTheory Set

namespace Paper26.GraphExperiment

open QuantumModel H1PosteriorBound

abbrev Parameter (r s : ℕ) := ParameterSpace (2 * r * s)
abbrev StateIndex (r s : ℕ) := Fin r ⊕ Fin s
abbrev CopyIndex (r s n : ℕ) := Fin n → StateIndex r s

variable {r s n : ℕ} [NeZero r]
variable {Y : Type*} [MeasurableSpace Y]

/-- The actual graph density at a real Euclidean parameter. -/
def state (θ : Parameter r s) : Density (StateIndex r s) :=
  GraphFamily.density ((MatrixCoordinates.coordinates r s).symm θ)

theorem continuous_state_matrix :
    Continuous (fun θ : Parameter r s => (state θ).matrix) :=
  GraphFamily.continuous_density_matrix.comp (MatrixCoordinates.coordinates r s).symm.continuous

/-- The graph states have the exact promised rank. -/
theorem state_rank (θ : Parameter r s) : (state θ).matrix.rank = r := by
  simpa only [state, Fintype.card_fin] using
    GraphFamily.density_rank ((MatrixCoordinates.coordinates r s).symm θ)

/-- The actual `n`-copy input density. -/
def copyState (θ : Parameter r s) : Density (CopyIndex r s n) :=
  TensorCopies.density (state θ) n

theorem continuous_copyState_entry (i j : CopyIndex r s n) :
    Continuous (fun θ : Parameter r s => (copyState θ).matrix i j) := by
  change Continuous (fun θ : Parameter r s => ∏ k : Fin n, (state θ).matrix (i k) (j k))
  exact continuous_finset_prod Finset.univ (fun k _ =>
    (continuous_apply_apply (i k) (j k)).comp continuous_state_matrix)

omit [NeZero r] in
/-- Finite matrix products preserve entrywise smoothness, using actual finite
sums rather than a choice of a global matrix norm. -/
theorem contDiff_mul_entry {u v w : Type*} [Fintype v]
    {k : WithTop ℕ∞} (F : Parameter r s → Matrix u v ℂ)
    (G : Parameter r s → Matrix v w ℂ)
    (hF : ∀ i j, ContDiff ℝ k (fun θ => F θ i j))
    (hG : ∀ i j, ContDiff ℝ k (fun θ => G θ i j)) (i : u) (j : w) :
    ContDiff ℝ k (fun θ => (F θ * G θ) i j) := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum (fun a _ => (hF i a).mul (hG a j))

omit [NeZero r] in
/-- The determinant is an actual finite polynomial in the entries. -/
theorem contDiff_det_entry {u : Type*} [Fintype u] [DecidableEq u]
    {k : WithTop ℕ∞} (F : Parameter r s → Matrix u u ℂ)
    (hF : ∀ i j, ContDiff ℝ k (fun θ => F θ i j)) :
    ContDiff ℝ k (fun θ => (F θ).det) := by
  simp only [Matrix.det_apply']
  exact ContDiff.sum (fun σ _ => contDiff_const.mul
    (contDiff_prod (fun i _ => hF (σ i) i)))

omit [NeZero r] in
/-- The adjugate entries are determinants of matrices with one constant row. -/
theorem contDiff_adjugate_entry {u : Type*} [Fintype u] [DecidableEq u]
    {k : WithTop ℕ∞} (F : Parameter r s → Matrix u u ℂ)
    (hF : ∀ i j, ContDiff ℝ k (fun θ => F θ i j)) (i j : u) :
    ContDiff ℝ k (fun θ => (F θ).adjugate i j) := by
  simp only [Matrix.adjugate_apply]
  apply contDiff_det_entry
  intro a b
  by_cases ha : a = j
  · subst a
    simp only [Matrix.updateRow_self]
    exact contDiff_const
  · simpa only [Matrix.updateRow_ne ha] using hF a b

omit [NeZero r] in
/-- Nonsingular matrix inversion is smooth entrywise by the native adjugate /
determinant formula. -/
theorem contDiff_inv_entry {u : Type*} [Fintype u] [DecidableEq u]
    {k : WithTop ℕ∞} (F : Parameter r s → Matrix u u ℂ)
    (hF : ∀ i j, ContDiff ℝ k (fun θ => F θ i j))
    (hdet : ∀ θ, (F θ).det ≠ 0) (i j : u) :
    ContDiff ℝ k (fun θ => (F θ)⁻¹ i j) := by
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul]
  exact ((contDiff_det_entry F hF).inv hdet).mul (contDiff_adjugate_entry F hF i j)

omit [NeZero r] in
theorem contDiff_coordinate_entry {k : WithTop ℕ∞} (i : Fin s) (j : Fin r) :
    ContDiff ℝ k (fun θ : Parameter r s => (MatrixCoordinates.coordinates r s).symm θ i j) :=
  contDiff_pi.mp (contDiff_pi.mp (MatrixCoordinates.coordinates r s).symm.contDiff i) j

omit [NeZero r] in
theorem contDiff_graph_columns_entry {k : WithTop ℕ∞} (i : StateIndex r s) (j : Fin r) :
    ContDiff ℝ k (fun θ : Parameter r s =>
      GraphFamily.columns ((MatrixCoordinates.coordinates r s).symm θ) i j) := by
  cases i with
  | inl i => exact contDiff_const
  | inr i => exact contDiff_coordinate_entry i j

omit [NeZero r] in
theorem contDiff_graph_metric_entry {k : WithTop ℕ∞} (i j : Fin r) :
    ContDiff ℝ k (fun θ : Parameter r s =>
      GraphFamily.metric ((MatrixCoordinates.coordinates r s).symm θ) i j) := by
  change ContDiff ℝ k (fun θ : Parameter r s => (1 : Matrix (Fin r) (Fin r) ℂ) i j +
    ∑ a : Fin s, star ((MatrixCoordinates.coordinates r s).symm θ a i) *
      (MatrixCoordinates.coordinates r s).symm θ a j)
  exact contDiff_const.add (ContDiff.sum (fun a _ =>
    (Complex.conjCLE.contDiff.comp (contDiff_coordinate_entry a i)).mul
      (contDiff_coordinate_entry a j)))

omit [NeZero r] in
theorem contDiff_graph_inverse_entry {k : WithTop ℕ∞} (i j : Fin r) :
    ContDiff ℝ k (fun θ : Parameter r s =>
      (GraphFamily.metric ((MatrixCoordinates.coordinates r s).symm θ))⁻¹ i j) :=
  contDiff_inv_entry _ contDiff_graph_metric_entry
    (fun _ => GraphFamily.metric_det_ne_zero _) i j

omit [NeZero r] in
theorem contDiff_graph_projector_entry {k : WithTop ℕ∞} (i j : StateIndex r s) :
    ContDiff ℝ k (fun θ : Parameter r s =>
      GraphFamily.projectorMatrix ((MatrixCoordinates.coordinates r s).symm θ) i j) := by
  apply contDiff_mul_entry _ _ _ _ i j
  · exact fun a b => contDiff_mul_entry _ _ contDiff_graph_columns_entry
      contDiff_graph_inverse_entry a b
  · intro a b
    exact Complex.conjCLE.contDiff.comp (contDiff_graph_columns_entry b a)

/-- The actual graph-state entries are smooth over the real coordinates. -/
theorem contDiff_state_entry {k : WithTop ℕ∞} (i j : StateIndex r s) :
    ContDiff ℝ k (fun θ : Parameter r s => (state θ).matrix i j) := by
  simp only [state, GraphFamily.density_matrix, Matrix.smul_apply]
  exact contDiff_const.smul (contDiff_graph_projector_entry i j)

theorem contDiff_copyState_entry {k : WithTop ℕ∞} (i j : CopyIndex r s n) :
    ContDiff ℝ k (fun θ : Parameter r s => (copyState θ).matrix i j) := by
  change ContDiff ℝ k (fun θ : Parameter r s =>
    ∏ a : Fin n, (state θ).matrix (i a) (j a))
  exact contDiff_prod (fun a _ => contDiff_state_entry (i a) (j a))

/-- The copy density has the flat-state quadratic identity. -/
theorem state_square (θ : Parameter r s) :
    (state θ).matrix * (state θ).matrix = (r : ℝ)⁻¹ • (state θ).matrix := by
  simp only [state, GraphFamily.density_matrix, Fintype.card_fin]
  rw [Matrix.smul_mul, Matrix.mul_smul, GraphFamily.projectorMatrix_idempotent]

omit [NeZero r] in
theorem tensor_real_smul (c : ℝ) (B : Matrix (StateIndex r s) (StateIndex r s) ℂ) :
    TensorCopies.matrix (c • B) n = c ^ n • TensorCopies.matrix B n := by
  ext i j
  simp only [TensorCopies.matrix, Matrix.smul_apply, Complex.real_smul,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Complex.ofReal_pow]

theorem copyState_square (θ : Parameter r s) :
    (copyState (n := n) θ).matrix * (copyState θ).matrix =
      ((r : ℝ)⁻¹) ^ n • (copyState θ).matrix := by
  change TensorCopies.matrix (state θ).matrix n * TensorCopies.matrix (state θ).matrix n = _
  rw [← TensorCopies.matrix_mul, state_square, tensor_real_smul]
  rfl

/-- A smooth, explicit amplitude for the actual `n`-copy input density. It is
`P_X / sqrt r` tensor `n` times, expressed as a scalar times the flat density. -/
def amplitude (θ : Parameter r s) : Matrix (CopyIndex r s n) (CopyIndex r s n) ℂ :=
  Real.sqrt ((r : ℝ) ^ n) • (copyState θ).matrix

theorem amplitude_gram (θ : Parameter r s) :
    amplitude (n := n) θ * (amplitude θ).conjTranspose = (copyState θ).matrix := by
  have hr : (r : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne r
  have hc : Real.sqrt ((r : ℝ) ^ n) ^ 2 * ((r : ℝ)⁻¹) ^ n = 1 := by
    rw [Real.sq_sqrt (pow_nonneg (Nat.cast_nonneg r) n), ← mul_pow,
      mul_inv_cancel₀ hr, one_pow]
  simp only [amplitude, Matrix.conjTranspose_smul, star_trivial,
    (copyState θ).positive.isHermitian.eq, Matrix.smul_mul, Matrix.mul_smul,
    copyState_square, smul_smul]
  rw [← mul_assoc, ← pow_two, hc, one_smul]

theorem contDiff_amplitude_entry {k : WithTop ℕ∞} (i j : CopyIndex r s n) :
    ContDiff ℝ k (fun θ : Parameter r s => amplitude θ i j) :=
  contDiff_const.smul (contDiff_copyState_entry i j)

/-- Put actual matrix entries in their finite Euclidean Frobenius space. -/
def matrixVector {u v : Type*} [Fintype u] [Fintype v] (B : Matrix u v ℂ) :
    EuclideanSpace ℂ (u × v) := WithLp.toLp 2 (fun ij => B ij.1 ij.2)

theorem matrixVector_norm_sq {u v : Type*} [Fintype u] [Fintype v] (B : Matrix u v ℂ) :
    ‖matrixVector B‖ ^ 2 = ShellAccounting.frobeniusSq B := by
  rw [EuclideanSpace.norm_sq_eq]
  change (∑ ij : u × v, ‖B ij.1 ij.2‖ ^ 2) = ∑ i : u, ∑ j : v, ‖B i j‖ ^ 2
  rw [Fintype.sum_prod_type]

theorem contDiff_matrixVector_amplitude {k : WithTop ℕ∞}
    (R : Matrix (CopyIndex r s n) (CopyIndex r s n) ℂ) :
    ContDiff ℝ k (fun θ : Parameter r s => matrixVector (R * amplitude θ)) := by
  apply PiLp.contDiff_toLp.comp
  apply contDiff_pi.2
  intro ij
  exact contDiff_mul_entry (fun _ : Parameter r s => R) _
    (fun _ _ => contDiff_const) contDiff_amplitude_entry ij.1 ij.2

variable (A : CollectiveModel.Learner (StateIndex r s) Y n)

/-- Born's genuine likelihood, relative to the learner's reference measure. -/
def likelihood (θ : Parameter r s) (y : Y) : ℝ := A.born (state θ) y

/-- The actual complex Born derivative, an integrable finite linear
combination of the POVM entries. -/
def complexLikelihoodDerivative (θ : Parameter r s) (y : Y) : Parameter r s →L[ℝ] ℂ :=
  ∑ i : CopyIndex r s n, ∑ j : CopyIndex r s n,
    A.measurement.effect y j i • fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i j) θ

/-- The real derivative candidate of the actual Born density. -/
def likelihoodDerivative (θ : Parameter r s) (y : Y) : Parameter r s →L[ℝ] ℝ :=
  Complex.reCLM.comp (complexLikelihoodDerivative A θ y)

/-- The genuine square-root likelihood, with the outcome first as required by
`WeakPosteriorIdentity`. Exceptional nonpositive effects do not alter any
reference-a.e. statement. -/
def likelihoodRoot (y : Y) (θ : Parameter r s) : ℝ := Real.sqrt (likelihood A θ y)

theorem likelihood_eq_sum (θ : Parameter r s) (y : Y) :
    likelihood A θ y =
      (∑ i : CopyIndex r s n, ∑ j : CopyIndex r s n,
        (copyState θ).matrix i j * A.measurement.effect y j i).re := by
  exact congrArg Complex.re (A.measurement.complexBorn_eq_sum (copyState θ) y)

theorem likelihood_measurable (θ : Parameter r s) : Measurable (likelihood A θ) :=
  A.born_measurable (state θ)

theorem likelihood_integrable (θ : Parameter r s) :
    Integrable (likelihood A θ) A.measurement.reference := A.born_integrable (state θ)

theorem likelihood_integral (θ : Parameter r s) :
    (∫ y, likelihood A θ y ∂A.measurement.reference) = 1 := A.born_integral (state θ)

/-- A common a.e. good-effect set works simultaneously for every parameter. -/
theorem likelihood_nonneg_all_ae :
    ∀ᵐ y ∂A.measurement.reference, ∀ θ : Parameter r s, 0 ≤ likelihood A θ y := by
  filter_upwards [A.measurement.positive_ae] with y hy θ
  exact A.measurement.born_nonneg (copyState θ) hy

theorem continuous_likelihood (y : Y) : Continuous (fun θ : Parameter r s => likelihood A θ y) := by
  simp_rw [likelihood_eq_sum]
  apply Complex.continuous_re.comp
  apply continuous_finset_sum Finset.univ
  intro i _
  exact continuous_finset_sum Finset.univ (fun j _ =>
    (continuous_copyState_entry i j).mul continuous_const)

/-- Born likelihoods themselves are smooth, including at zero probability.
The square-root regularity at zeros is a distinct issue. -/
theorem contDiff_likelihood {k : WithTop ℕ∞} (y : Y) :
    ContDiff ℝ k (fun θ : Parameter r s => likelihood A θ y) := by
  simp_rw [likelihood_eq_sum]
  exact Complex.reCLM.contDiff.comp (ContDiff.sum (fun i _ =>
    ContDiff.sum (fun j _ => (contDiff_copyState_entry i j).mul contDiff_const)))

set_option maxHeartbeats 800000 in
theorem complexLikelihoodDerivative_integrable (θ : Parameter r s) :
    Integrable (complexLikelihoodDerivative A θ) A.measurement.reference := by
  exact integrable_finset_sum Finset.univ
    (f := fun i y => ∑ j : CopyIndex r s n,
      A.measurement.effect y j i •
        fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i j) θ)
    (fun i _ => integrable_finset_sum Finset.univ
      (f := fun j y => A.measurement.effect y j i •
        fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i j) θ)
      (fun j _ => (A.measurement.entry_integrable j i).smul_const _))

theorem likelihood_hasFDerivAt (θ : Parameter r s) (y : Y) :
    HasFDerivAt (fun t : Parameter r s => likelihood A t y) (likelihoodDerivative A θ y) θ := by
  simp only [likelihoodDerivative, complexLikelihoodDerivative]
  simp_rw [likelihood_eq_sum]
  exact Complex.reCLM.hasFDerivAt.comp θ (HasFDerivAt.fun_sum (fun i _ =>
    HasFDerivAt.fun_sum (fun j _ =>
      ((contDiff_copyState_entry (k := 1) i j).differentiable_one θ).hasFDerivAt.mul_const _)))

/-- Integrability of the Born derivative is proved entrywise from the actual
POVM, before any posterior or score identity is invoked. -/
theorem likelihoodDerivative_integrable (θ : Parameter r s) :
    Integrable (likelihoodDerivative A θ) A.measurement.reference :=
  ((ContinuousLinearMap.compL ℝ (Parameter r s) ℂ ℝ) Complex.reCLM).integrable_comp
    (complexLikelihoodDerivative_integrable A θ)

/-- The derivative integral is zero because integrating the effects gives the
identity and differentiating the actual input trace gives zero. -/
theorem complexLikelihoodDerivative_integral (θ : Parameter r s) :
    (∫ y, complexLikelihoodDerivative A θ y ∂A.measurement.reference) = 0 := by
  have hi : ∀ i j : CopyIndex r s n, Integrable
      (fun y => A.measurement.effect y j i •
        fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i j) θ)
      A.measurement.reference := fun i j => (A.measurement.entry_integrable j i).smul_const _
  have hd : (∑ i : CopyIndex r s n,
      fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i i) θ) = 0 := by
    have ht : HasFDerivAt (fun t : Parameter r s => Matrix.trace (copyState (n := n) t).matrix)
        (∑ i : CopyIndex r s n,
          fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i i) θ) θ := by
      exact HasFDerivAt.fun_sum (fun i _ =>
        ((contDiff_copyState_entry (k := 1) i i).differentiable_one θ).hasFDerivAt)
    have he : (fun t : Parameter r s => Matrix.trace (copyState (n := n) t).matrix) = fun _ => (1 : ℂ) :=
      funext (fun t => (copyState (n := n) t).trace_one)
    rw [he] at ht
    exact ht.unique (hasFDerivAt_const 1 θ)
  unfold complexLikelihoodDerivative
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_finset_sum Finset.univ (fun j _ => hi i j))]
  simp_rw [integral_finset_sum Finset.univ (fun j _ => hi _ j), integral_smul_const,
    A.measurement.total]
  have he : ∀ i j : CopyIndex r s n,
      (1 : Matrix (CopyIndex r s n) (CopyIndex r s n) ℂ) j i •
        fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i j) θ =
      if j = i then fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i i) θ else 0 := by
    intro i j
    by_cases hij : j = i
    · subst j
      simp
    · rw [if_neg hij, Matrix.one_apply_ne hij]
      exact zero_smul ℂ
        (fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i j) θ)
  simp_rw [he]
  simpa using hd

theorem likelihoodDerivative_integral (θ : Parameter r s) :
    (∫ y, likelihoodDerivative A θ y ∂A.measurement.reference) = 0 := by
  change (∫ y, ((ContinuousLinearMap.compL ℝ (Parameter r s) ℂ ℝ) Complex.reCLM)
    (complexLikelihoodDerivative A θ y) ∂A.measurement.reference) = 0
  rw [ContinuousLinearMap.integral_comp_comm _ (complexLikelihoodDerivative_integrable A θ),
    complexLikelihoodDerivative_integral, map_zero]

/-- Genuine finite-matrix differentiation under the Born integral. Both the
integrand's derivative and its integrability were proved above. -/
theorem hasFDerivAt_integral_likelihood (θ : Parameter r s) :
    HasFDerivAt (fun t : Parameter r s => ∫ y, likelihood A t y ∂A.measurement.reference)
      (∫ y, likelihoodDerivative A θ y ∂A.measurement.reference) θ := by
  rw [likelihoodDerivative_integral]
  have he : (fun t : Parameter r s => ∫ y, likelihood A t y ∂A.measurement.reference) =
      fun _ => (1 : ℝ) := funext (likelihood_integral A)
  rw [he]
  exact hasFDerivAt_const 1 θ

theorem complexLikelihoodDerivative_joint_measurable :
    Measurable (fun z : Y × Parameter r s => complexLikelihoodDerivative A z.2 z.1) := by
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    Finset.measurable_sum Finset.univ (fun j _ =>
      ((A.measurement.entry_measurable j i).comp measurable_fst).smul
        (((contDiff_copyState_entry (k := 1) i j).continuous_fderiv le_rfl).measurable.comp
          measurable_snd)))

theorem likelihoodDerivative_joint_measurable :
    Measurable (fun z : Y × Parameter r s => likelihoodDerivative A z.2 z.1) :=
  ((ContinuousLinearMap.compL ℝ (Parameter r s) ℂ ℝ) Complex.reCLM).continuous.measurable.comp
    (complexLikelihoodDerivative_joint_measurable A)

theorem likelihood_joint_measurable :
    Measurable (fun z : Y × Parameter r s => likelihood A z.2 z.1) := by
  simp_rw [likelihood_eq_sum]
  apply Complex.continuous_re.measurable.comp
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    Finset.measurable_sum Finset.univ (fun j _ =>
      ((continuous_copyState_entry i j).measurable.comp measurable_snd).mul
        ((A.measurement.entry_measurable j i).comp measurable_fst)))

theorem likelihoodRoot_nonneg (y : Y) (θ : Parameter r s) : 0 ≤ likelihoodRoot A y θ :=
  Real.sqrt_nonneg _

theorem continuous_likelihoodRoot (y : Y) :
    Continuous (likelihoodRoot A y) := Real.continuous_sqrt.comp (continuous_likelihood A y)

theorem likelihoodRoot_measurable (θ : Parameter r s) :
    Measurable (fun y => likelihoodRoot A y θ) :=
  Real.continuous_sqrt.measurable.comp (likelihood_measurable A θ)

theorem likelihoodRoot_joint_measurable :
    Measurable (fun z : Y × Parameter r s => likelihoodRoot A z.1 z.2) :=
  Real.continuous_sqrt.measurable.comp (likelihood_joint_measurable A)

/-- The totalized classical square-root derivative has an explicit formula
even at zero likelihood: its value there is zero because the nonnegative
square-root function has a minimum. No positivity assumption on exceptional
POVM effects is needed for this formula. -/
theorem likelihoodRoot_fderiv (y : Y) (θ : Parameter r s) :
    fderiv ℝ (likelihoodRoot A y) θ =
      (1 / (2 * likelihoodRoot A y θ)) • likelihoodDerivative A θ y := by
  by_cases hz : likelihood A θ y = 0
  · have hgzero : likelihoodRoot A y θ = 0 := by simp only [likelihoodRoot, hz, Real.sqrt_zero]
    have hmin : IsLocalMin (likelihoodRoot A y) θ :=
      Filter.Eventually.of_forall (fun t => by rw [hgzero]; exact likelihoodRoot_nonneg A y t)
    rw [hmin.fderiv_eq_zero, hgzero, mul_zero, div_zero, zero_smul]
  · exact ((likelihood_hasFDerivAt A θ y).sqrt hz).fderiv

/-- Joint gradient measurability is proved from the actual finite matrix
formula, rather than imposed as an experiment assumption. -/
theorem likelihoodRoot_fderiv_joint_measurable :
    Measurable (fun z : Y × Parameter r s => fderiv ℝ (likelihoodRoot A z.1) z.2) := by
  simp_rw [likelihoodRoot_fderiv]
  exact (measurable_const.div (measurable_const.mul (likelihoodRoot_joint_measurable A))).smul
    (likelihoodDerivative_joint_measurable A)

theorem likelihoodRoot_sq_all_ae :
    ∀ᵐ y ∂A.measurement.reference, ∀ θ : Parameter r s,
      likelihoodRoot A y θ ^ 2 = likelihood A θ y := by
  filter_upwards [likelihood_nonneg_all_ae A] with y hy θ
  exact Real.sq_sqrt (hy θ)

theorem likelihoodRoot_sq_integrable (θ : Parameter r s) :
    Integrable (fun y => likelihoodRoot A y θ ^ 2) A.measurement.reference := by
  apply (likelihood_integrable A θ).congr
  exact (likelihoodRoot_sq_all_ae A).mono (fun _ hy => (hy θ).symm)

theorem likelihoodRoot_sq_integral (θ : Parameter r s) :
    (∫ y, likelihoodRoot A y θ ^ 2 ∂A.measurement.reference) = 1 := by
  calc
    _ = ∫ y, likelihood A θ y ∂A.measurement.reference :=
      integral_congr_ae ((likelihoodRoot_sq_all_ae A).mono (fun _ hy => hy θ))
    _ = 1 := likelihood_integral A θ

theorem likelihoodRoot_sq_lintegral (θ : Parameter r s) :
    (∫⁻ y, ENNReal.ofReal (likelihoodRoot A y θ ^ 2) ∂A.measurement.reference) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (likelihoodRoot_sq_integrable A θ)
    (Filter.Eventually.of_forall (fun _ => sq_nonneg _)),
    likelihoodRoot_sq_integral A θ, ENNReal.ofReal_one]

theorem likelihoodRoot_memLp_two (θ : Parameter r s) :
    MemLp (fun y => likelihoodRoot A y θ) 2 A.measurement.reference :=
  (memLp_two_iff_integrable_sq (likelihoodRoot_measurable A θ).aestronglyMeasurable).2
    (likelihoodRoot_sq_integrable A θ)

/-- A positive effect's Gram factor realizes the actual likelihood root as
the Frobenius norm of its matrix amplitude, including at zero likelihood. -/
theorem likelihoodRoot_eq_amplitude_norm {y : Y}
    (R : Matrix (CopyIndex r s n) (CopyIndex r s n) ℂ)
    (hR : R.conjTranspose * R = A.measurement.effect y) (θ : Parameter r s) :
    likelihoodRoot A y θ = ‖matrixVector (R * amplitude θ)‖ := by
  have he : ‖matrixVector (R * amplitude θ)‖ ^ 2 = likelihood A θ y := by
    rw [matrixVector_norm_sq, ShellAccounting.frobeniusSq_eq_trace', Matrix.conjTranspose_mul]
    have hm : (amplitude θ).conjTranspose * R.conjTranspose * (R * amplitude θ) =
        (amplitude θ).conjTranspose * A.measurement.effect y * amplitude θ := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc R.conjTranspose R, hR]
    rw [hm, Matrix.trace_mul_cycle, amplitude_gram]
    rfl
  rw [likelihoodRoot, ← he, Real.sqrt_sq (norm_nonneg _)]

/-- The actual quantum square-root likelihood is locally Lipschitz at every
parameter for every positive effect, by its smooth finite matrix amplitude. -/
theorem locallyLipschitz_likelihoodRoot {y : Y}
    (hy : (A.measurement.effect y).PosSemidef) : LocallyLipschitz (likelihoodRoot A y) := by
  obtain ⟨R, hR⟩ := TensorCopies.psd_exists_gram _ hy
  have he : likelihoodRoot A y = fun θ : Parameter r s => ‖matrixVector (R * amplitude θ)‖ :=
    funext (likelihoodRoot_eq_amplitude_norm A R hR)
  rw [he]
  exact lipschitzWith_one_norm.locallyLipschitz.comp
    (contDiff_matrixVector_amplitude (k := 1) R).locallyLipschitz

theorem locallyLipschitz_likelihoodRoot_ae :
    ∀ᵐ y ∂A.measurement.reference, LocallyLipschitz (likelihoodRoot A y) :=
  A.measurement.positive_ae.mono (fun _ hy => locallyLipschitz_likelihoodRoot A hy)

/-- At a good effect the square-root score is exactly the Born derivative,
including zero likelihoods. The zero case uses the local-minimum derivative
theorem; no square-root differentiability is asserted at a zero. -/
theorem likelihoodRoot_score_eq {y : Y} (hy : (A.measurement.effect y).PosSemidef)
    (θ : Parameter r s) :
    (2 * likelihoodRoot A y θ) • fderiv ℝ (likelihoodRoot A y) θ =
      likelihoodDerivative A θ y := by
  have hnon : ∀ t : Parameter r s, 0 ≤ likelihood A t y :=
    fun t => A.measurement.born_nonneg (copyState t) hy
  by_cases hz : likelihood A θ y = 0
  · have hmin : IsLocalMin (fun t : Parameter r s => likelihood A t y) θ :=
      Filter.Eventually.of_forall (fun t => by
        change likelihood A θ y ≤ likelihood A t y
        rw [hz]
        exact hnon t)
    have hd := hmin.hasFDerivAt_eq_zero (likelihood_hasFDerivAt A θ y)
    simp only [likelihoodRoot, hz, Real.sqrt_zero, mul_zero, zero_smul, hd]
  · have hg : DifferentiableAt ℝ (likelihoodRoot A y) θ :=
      (likelihood_hasFDerivAt A θ y).differentiableAt.sqrt hz
    have he : (fun t : Parameter r s => likelihoodRoot A y t ^ 2) =
        fun t => likelihood A t y := funext (fun t => Real.sq_sqrt (hnon t))
    have hp := hg.hasFDerivAt.pow 2
    rw [he] at hp
    have hd := hp.unique (likelihood_hasFDerivAt A θ y)
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, two_smul, two_mul] using hd

/-- The actual square-root score is integrable for every parameter, since it
agrees a.e. with the already integrable finite-matrix Born derivative. -/
theorem likelihoodRoot_score_integrable (θ : Parameter r s) :
    Integrable (fun y => (2 * likelihoodRoot A y θ) • fderiv ℝ (likelihoodRoot A y) θ)
      A.measurement.reference := by
  apply (likelihoodDerivative_integrable A θ).congr
  exact A.measurement.positive_ae.mono (fun _ hy => (likelihoodRoot_score_eq A hy θ).symm)

/-- The derivative of the normalized squared-root outcome integral equals the
integral of its actual score. This is the precise `hdiff` hypothesis consumed
by the weak posterior theorem, proved here from finite matrices. -/
theorem hasFDerivAt_integral_likelihoodRoot_sq (θ : Parameter r s) :
    HasFDerivAt (fun t : Parameter r s => ∫ y, likelihoodRoot A y t ^ 2 ∂A.measurement.reference)
      (∫ y, (2 * likelihoodRoot A y θ) • fderiv ℝ (likelihoodRoot A y) θ
        ∂A.measurement.reference) θ := by
  have hs : (∫ y, (2 * likelihoodRoot A y θ) • fderiv ℝ (likelihoodRoot A y) θ
      ∂A.measurement.reference) = 0 := by
    calc
      _ = ∫ y, likelihoodDerivative A θ y ∂A.measurement.reference :=
        integral_congr_ae (A.measurement.positive_ae.mono
          (fun _ hy => likelihoodRoot_score_eq A hy θ))
      _ = 0 := likelihoodDerivative_integral A θ
  rw [hs]
  have he : (fun t : Parameter r s => ∫ y, likelihoodRoot A y t ^ 2 ∂A.measurement.reference) =
      fun _ => (1 : ℝ) := funext (likelihoodRoot_sq_integral A)
  rw [he]
  exact hasFDerivAt_const 1 θ

/-- The integral of the actual squared roots is a constant smooth function.
This proves differentiability of the normalized integral. Identifying its zero
derivative with the integral of the pointwise square-root score is the
separate differentiation-under-the-integral obligation below. -/
theorem normalized_integral_hasFDerivAt (θ : Parameter r s) :
    HasFDerivAt (𝕜 := ℝ)
      (fun t => ∫ y, likelihoodRoot A y t ^ 2 ∂A.measurement.reference) 0 θ := by
  have he : (fun t : Parameter r s => ∫ y, likelihoodRoot A y t ^ 2 ∂A.measurement.reference) =
      fun _ => (1 : ℝ) := funext (likelihoodRoot_sq_integral A)
  rw [he]
  exact hasFDerivAt_const 1 θ

/-- The actual outcome law equals the probability law defined from the
square-root likelihood, with no abstract replacement density. -/
theorem outcomeMeasure_eq_root_density (θ : Parameter r s) :
    A.outcomeMeasure (state θ) = A.measurement.reference.withDensity
      (fun y => ENNReal.ofReal (likelihoodRoot A y θ ^ 2)) := by
  apply withDensity_congr_ae
  filter_upwards [likelihoodRoot_sq_all_ae A] with y hy
  change ENNReal.ofReal (likelihood A θ y) = ENNReal.ofReal (likelihoodRoot A y θ ^ 2)
  exact congrArg ENNReal.ofReal (hy θ).symm

/-- The actual prior/experiment Bayes marginal. -/
def bayesMarginal (h : WeakH1Root (2 * r * s)) : Y → ℝ≥0∞ :=
  WeakPosteriorIdentity.marginal h (likelihoodRoot A)

theorem bayesMarginal_aemeasurable (h : WeakH1Root (2 * r * s)) :
    AEMeasurable (bayesMarginal A h) A.measurement.reference :=
  WeakPosteriorIdentity.marginal_aemeasurable A.measurement.reference h _
    (WeakPosteriorIdentity.jointDensity_aemeasurable A.measurement.reference h _
      (likelihoodRoot_joint_measurable A).aestronglyMeasurable)

theorem bayesMarginal_integral_one (h : WeakH1Root (2 * r * s))
    (hh : h.mass univ = 1) : (∫⁻ y, bayesMarginal A h y ∂A.measurement.reference) = 1 := by
  exact WeakPosteriorIdentity.marginal_integral_one A.measurement.reference h _
    (WeakPosteriorIdentity.jointDensity_aemeasurable A.measurement.reference h _
      (likelihoodRoot_joint_measurable A).aestronglyMeasurable)
    (fun θ => ENNReal.continuous_ofReal.measurable.comp_aemeasurable
      ((likelihoodRoot_measurable A θ).pow_const 2).aemeasurable)
    (likelihoodRoot_sq_lintegral A) hh

/-- The actual marginal law is a probability measure when the prior is
normalized. -/
def bayesOutcomeMeasure (h : WeakH1Root (2 * r * s)) : Measure Y :=
  A.measurement.reference.withDensity (bayesMarginal A h)

theorem bayesOutcomeMeasure_univ (h : WeakH1Root (2 * r * s))
    (hh : h.mass univ = 1) : bayesOutcomeMeasure A h univ = 1 := by
  rw [bayesOutcomeMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact bayesMarginal_integral_one A h hh

/-- A finite uniform actual Fisher-energy bound implies the local-energy
hypothesis. This is a native integration bridge for subsequent quantum budget
proofs, not a supplied posterior-information conclusion. -/
theorem localEnergy_of_uniform_bound {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ᵐ θ ∂(volume : Measure (Parameter r s)),
      (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference) ≤ C)
    (k : ℕ) :
    (∫⁻ θ in Metric.closedBall (0 : Parameter r s) (k : ℝ),
      (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference)) ≠ ∞ := by
  have hb : (∫⁻ θ in Metric.closedBall (0 : Parameter r s) (k : ℝ),
      (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference)) ≤
      C * volume (Metric.closedBall (0 : Parameter r s) (k : ℝ)) := by
    calc
      _ ≤ ∫⁻ _θ in Metric.closedBall (0 : Parameter r s) (k : ℝ), C :=
        lintegral_mono_ae (ae_restrict_of_ae hbound)
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hC (isCompact_closedBall (x := (0 : Parameter r s)) (r := (k : ℝ))).measure_lt_top.ne) hb

/-- The actual Bayes weak root for the collective graph experiment. -/
def posterior (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (h : WeakH1Root (2 * r * s)) : Y → WeakH1Root (2 * r * s) :=
  WeakPosteriorIdentity.bayesPosterior P h (likelihoodRoot A)

theorem posterior_normalized_ae
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (h : WeakH1Root (2 * r * s)) :
    ∀ᵐ y ∂A.measurement.reference,
      bayesMarginal A h y ≠ 0 → (posterior A P h y).mass univ = 1 := by
  filter_upwards [locallyLipschitz_likelihoodRoot_ae A] with y hy hm
  exact WeakPosteriorIdentity.bayesPosterior_normalized P h (likelihoodRoot A) hy hm

/-- Every regularity hypothesis of the weak posterior identity except local
energy has been derived above from actual finite quantum matrices. This final
bridge states the remaining local energy obligation openly. -/
theorem posterior_information_identity_of_localEnergy
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (h : WeakH1Root (2 * r * s))
    (hlocal : ∀ k : ℕ,
      (∫⁻ θ in Metric.closedBall (0 : Parameter r s) (k : ℝ),
        (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference)) ≠ ∞) :
    (∫⁻ y, bayesMarginal A h y * (posterior A P h y).fisher ∂A.measurement.reference) =
      h.fisher + WeakPosteriorIdentity.dataInformation A.measurement.reference h
        (likelihoodRoot A) := by
  apply WeakPosteriorIdentity.bayes_information_identity_of_local_energy
    A.measurement.reference P U h (likelihoodRoot A)
    (locallyLipschitz_likelihoodRoot_ae A)
    (fun θ => (likelihoodRoot_measurable A θ).aestronglyMeasurable)
    (likelihoodRoot_joint_measurable A).aestronglyMeasurable
    (likelihoodRoot_fderiv_joint_measurable A).aestronglyMeasurable
    (likelihoodRoot_sq_lintegral A)
    (fun k => Metric.closedBall 0 (k : ℝ))
    (fun _ => Metric.isClosed_closedBall.measurableSet) _ hlocal
    (Filter.Eventually.of_forall (hasFDerivAt_integral_likelihoodRoot_sq A))
  intro θ
  obtain ⟨k, hk⟩ := exists_nat_gt ‖θ‖
  exact ⟨k, by simpa only [Metric.mem_closedBall, dist_zero_right] using hk.le⟩

/-- A finite Fisher-energy budget supplies the sole remaining analytic energy
hypothesis in the actual graph experiment. -/
theorem posterior_information_identity_of_uniform_bound
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (h : WeakH1Root (2 * r * s)) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hbound : ∀ᵐ θ ∂(volume : Measure (Parameter r s)),
      (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference) ≤ C) :
    (∫⁻ y, bayesMarginal A h y * (posterior A P h y).fisher ∂A.measurement.reference) =
      h.fisher + WeakPosteriorIdentity.dataInformation A.measurement.reference h
        (likelihoodRoot A) :=
  posterior_information_identity_of_localEnergy A P U h (localEnergy_of_uniform_bound A hC hbound)

/-! The core through `bayesOutcomeMeasure_univ` was frozen before this
append-only local-energy completion. The following arguments bound actual
square-root derivative energies by the integrable effect trace. -/

theorem matrixVector_sub {u v : Type*} [Fintype u] [Fintype v]
    (B D : Matrix u v ℂ) : matrixVector (B - D) = matrixVector B - matrixVector D := rfl

open scoped NNReal

open scoped Matrix.Norms.Frobenius in
theorem matrixVector_norm_frobenius_eq {u v : Type*} [Fintype u] [Fintype v]
    (D : Matrix u v ℂ) : ‖matrixVector D‖ = ‖D‖ := by
  rw [EuclideanSpace.norm_eq, Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]
  simp only [Real.rpow_two]
  congr 1
  change (∑ ij : u × v, ‖D ij.1 ij.2‖ ^ 2) = ∑ i : u, ∑ j : v, ‖D i j‖ ^ 2
  rw [Fintype.sum_prod_type]

open scoped Matrix.Norms.Frobenius in
/-- Native Frobenius submultiplicativity in the fixed Euclidean entry space. -/
theorem matrixVector_norm_mul_le {u v w : Type*} [Fintype u] [Fintype v] [Fintype w]
    (R : Matrix u v ℂ) (B : Matrix v w ℂ) :
    ‖matrixVector (R * B)‖ ≤ ‖matrixVector R‖ * ‖matrixVector B‖ := by
  rw [matrixVector_norm_frobenius_eq, matrixVector_norm_frobenius_eq,
    matrixVector_norm_frobenius_eq]
  exact Matrix.frobenius_norm_mul R B

/-- A matrix amplitude's Lipschitz constant is multiplied by the Gram
factor's Frobenius norm before taking the scalar norm. -/
theorem lipschitzOnWith_amplitude_norm
    (R : Matrix (CopyIndex r s n) (CopyIndex r s n) ℂ)
    {S : Set (Parameter r s)} {C : ℝ≥0}
    (hamp : LipschitzOnWith C (fun θ : Parameter r s => matrixVector (amplitude (n := n) θ)) S) :
    LipschitzOnWith (‖matrixVector R‖₊ * C)
      (fun θ : Parameter r s => ‖matrixVector (R * amplitude θ)‖) S := by
  apply lipschitzOnWith_iff_dist_le_mul.2
  intro x hx z hz
  have hv : ∀ B D : Matrix (CopyIndex r s n) (CopyIndex r s n) ℂ,
      matrixVector (R * B) - matrixVector (R * D) = matrixVector (R * (B - D)) := by
    intro B D
    rw [Matrix.mul_sub, matrixVector_sub]
  calc
    dist ‖matrixVector (R * amplitude x)‖ ‖matrixVector (R * amplitude z)‖ ≤
        ‖matrixVector (R * amplitude x) - matrixVector (R * amplitude z)‖ :=
      dist_norm_norm_le _ _
    _ = ‖matrixVector (R * (amplitude x - amplitude z))‖ := by rw [hv]
    _ ≤ ‖matrixVector R‖ * ‖matrixVector (amplitude x - amplitude z)‖ :=
      matrixVector_norm_mul_le _ _
    _ = ‖matrixVector R‖ * dist (matrixVector (amplitude x)) (matrixVector (amplitude z)) := by
      rw [matrixVector_sub, dist_eq_norm]
    _ ≤ ‖matrixVector R‖ * ((C : ℝ) * dist x z) :=
      mul_le_mul_of_nonneg_left (hamp.dist_le_mul x hx z hz) (norm_nonneg _)
    _ = (‖matrixVector R‖₊ * C : ℝ≥0) * dist x z := by
      simp only [NNReal.coe_mul, coe_nnnorm]
      ring

/-- Smoothness gives a finite amplitude Lipschitz constant on each enlarged
closed ball. This constant is independent of the measurement outcome. -/
theorem amplitude_lipschitz_on_closedBall (k : ℕ) :
    ∃ C : ℝ≥0, LipschitzOnWith C
      (fun θ : Parameter r s => matrixVector (amplitude (n := n) θ))
      (Metric.closedBall 0 ((k : ℝ) + 1)) := by
  let f := fun θ : Parameter r s => matrixVector (amplitude (n := n) θ)
  have hf : ContDiff ℝ 1 f := by
    simpa only [Matrix.one_mul] using
      contDiff_matrixVector_amplitude (r := r) (s := s) (n := n) (k := 1) 1
  have hc : Continuous (fun θ : Parameter r s => ‖fderiv ℝ f θ‖₊) :=
    (hf.continuous_fderiv le_rfl).nnnorm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (x := (0 : Parameter r s))
    (r := (k : ℝ) + 1)).bddAbove_image hc.continuousOn
  refine ⟨C, Convex.lipschitzOnWith_of_nnnorm_fderiv_le (fun θ _ => hf.differentiable_one θ) ?_
    (convex_closedBall 0 ((k : ℝ) + 1))⟩
  intro θ hθ
  exact hC ⟨θ, hθ, rfl⟩

/-- The local squared derivative is bounded by a constant times the actual
effect trace. The constant depends on the compact parameter ball, never on the
outcome. Positive effects supply a Gram factor separately at each outcome. -/
theorem local_gradient_trace_bound (k : ℕ) :
    ∃ C : ℝ≥0, ∀ᵐ y ∂A.measurement.reference, ∀ θ : Parameter r s,
      θ ∈ Metric.closedBall 0 (k : ℝ) →
      ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ 2 ≤
        (C : ℝ) ^ 2 * (Matrix.trace (A.measurement.effect y)).re := by
  obtain ⟨C, hC⟩ := amplitude_lipschitz_on_closedBall (r := r) (s := s) (n := n) k
  refine ⟨C, ?_⟩
  filter_upwards [A.measurement.positive_ae] with y hy θ hθ
  obtain ⟨R, hR⟩ := TensorCopies.psd_exists_gram _ hy
  have hRtrace : ‖matrixVector R‖ ^ 2 = (Matrix.trace (A.measurement.effect y)).re := by
    rw [matrixVector_norm_sq, ShellAccounting.frobeniusSq_eq_trace', hR]
  have hroot : likelihoodRoot A y = fun t : Parameter r s => ‖matrixVector (R * amplitude t)‖ :=
    funext (likelihoodRoot_eq_amplitude_norm A R hR)
  have hLip := lipschitzOnWith_amplitude_norm R hC
  rw [← hroot] at hLip
  have hθ' : θ ∈ Metric.ball (0 : Parameter r s) ((k : ℝ) + 1) := by
    have hh : ‖θ‖ ≤ (k : ℝ) := by simpa only [Metric.mem_closedBall, dist_zero_right] using hθ
    have ht : ‖θ‖ < (k : ℝ) + 1 := by linarith
    simpa only [Metric.mem_ball, dist_zero_right] using ht
  have hd := norm_fderiv_le_of_lipschitzOn ℝ (Metric.closedBall_mem_nhds_of_mem hθ') hLip
  calc
    ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ 2 ≤ (‖matrixVector R‖ * (C : ℝ)) ^ 2 := by
      exact pow_le_pow_left₀ (norm_nonneg _) hd 2
    _ = (C : ℝ) ^ 2 * (Matrix.trace (A.measurement.effect y)).re := by
      rw [mul_pow, hRtrace]
      ring

omit [NeZero r] in
/-- The effect trace is integrable by the POVM's genuine diagonal entries. -/
theorem effectTrace_integrable :
    Integrable (fun y => (Matrix.trace (A.measurement.effect y)).re) A.measurement.reference := by
  have hi : Integrable (fun y => Matrix.trace (A.measurement.effect y)) A.measurement.reference :=
    integrable_finset_sum Finset.univ (fun i _ => A.measurement.entry_integrable i i)
  exact hi.re

omit [NeZero r] in
theorem effectTrace_nonneg_ae :
    ∀ᵐ y ∂A.measurement.reference, 0 ≤ (Matrix.trace (A.measurement.effect y)).re :=
  A.measurement.positive_ae.mono (fun _ hy => (Complex.nonneg_iff.mp hy.trace_nonneg).1)

/-- Local squared gradient energy is finite for every actual finite dominated
collective graph experiment. All norm and integration bounds are proved from
the explicit smooth amplitude and the integrable positive effect trace. -/
theorem localEnergy_finite (k : ℕ) :
    (∫⁻ θ in Metric.closedBall (0 : Parameter r s) (k : ℝ),
      (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference)) ≠ ∞ := by
  obtain ⟨C, hC⟩ := local_gradient_trace_bound A k
  let J : ℝ≥0∞ := ENNReal.ofReal ((C : ℝ) ^ 2) *
    (∫⁻ y, ENNReal.ofReal (Matrix.trace (A.measurement.effect y)).re ∂A.measurement.reference)
  have hJ : J ≠ ∞ := by
    apply ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    exact (lintegral_ofReal_ne_top_iff_integrable (effectTrace_integrable A).aestronglyMeasurable
      (effectTrace_nonneg_ae A)).2 (effectTrace_integrable A)
  have hb : ∀ θ ∈ Metric.closedBall (0 : Parameter r s) (k : ℝ),
      (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference) ≤ J := by
    intro θ hθ
    calc
      _ ≤ ∫⁻ y, ENNReal.ofReal ((C : ℝ) ^ 2) *
          ENNReal.ofReal (Matrix.trace (A.measurement.effect y)).re ∂A.measurement.reference := by
        apply lintegral_mono_ae
        filter_upwards [hC] with y hy
        rw [WeakPosteriorIdentity.enorm_sq_eq_ofReal_norm_sq,
          ← ENNReal.ofReal_mul (sq_nonneg (C : ℝ))]
        exact ENNReal.ofReal_le_ofReal (hy θ hθ)
      _ = J := by
        exact lintegral_const_mul'' _
          (effectTrace_integrable A).aestronglyMeasurable.aemeasurable.ennreal_ofReal
  have hlocal : (∫⁻ θ in Metric.closedBall (0 : Parameter r s) (k : ℝ),
      (∫⁻ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ₑ ^ (2 : ℕ) ∂A.measurement.reference)) ≤
      J * volume (Metric.closedBall (0 : Parameter r s) (k : ℝ)) := by
    calc
      _ ≤ ∫⁻ _θ in Metric.closedBall (0 : Parameter r s) (k : ℝ), J := by
        apply lintegral_mono_ae
        apply (ae_restrict_iff' Metric.isClosed_closedBall.measurableSet).2
        exact Filter.Eventually.of_forall hb
      _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ]
  exact ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hJ (isCompact_closedBall (x := (0 : Parameter r s))
      (r := (k : ℝ))).measure_lt_top.ne) hlocal

/-- The general posterior-information identity specialized to the actual
collective graph experiment. No experiment regularity or posterior identity is
assumed: only the two independent classical weak-Sobolev facts are parameters. -/
theorem posterior_information_identity
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (h : WeakH1Root (2 * r * s)) :
    (∫⁻ y, bayesMarginal A h y * (posterior A P h y).fisher ∂A.measurement.reference) =
      h.fisher + WeakPosteriorIdentity.dataInformation A.measurement.reference h
        (likelihoodRoot A) :=
  posterior_information_identity_of_localEnergy A P U h (localEnergy_finite A)

/-- Actual Born success integrated against the actual prior density, with
outcomes integrated first. The successful parameter sets may depend on the
learner's outcome. -/
def bornSuccess (h : WeakH1Root (2 * r * s)) (S : Y → Set (Parameter r s)) : ℝ≥0∞ :=
  ∫⁻ y, (∫⁻ θ in S y, ENNReal.ofReal (h.root θ ^ 2) *
    ENNReal.ofReal (likelihood A θ y)) ∂A.measurement.reference

/-- The prior-average of the learner's actual Born probability of success.
Joint success-event measurability will be required to relate the two orders of
integration and to interpret every event as measurable. -/
def priorAverageSuccess (h : WeakH1Root (2 * r * s))
    (S : Y → Set (Parameter r s)) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) *
    A.outcomeMeasure (state θ) {y | θ ∈ S y}

/-- Bayes cancellation for actual posterior mass, including zero marginals.
This is a measure identity, independent of the Fisher-information identity. -/
theorem posterior_weighted_mass_eq_born_ae
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (h : WeakH1Root (2 * r * s)) (S : Y → Set (Parameter r s)) :
    ∀ᵐ y ∂A.measurement.reference,
      bayesMarginal A h y * (posterior A P h y).mass (S y) =
        ∫⁻ θ in S y, ENNReal.ofReal (h.root θ ^ 2) * ENNReal.ofReal (likelihood A θ y) := by
  filter_upwards [A.measurement.positive_ae] with y hy
  let K := WeakPosteriorIdentity.weakProductRoot P h (likelihoodRoot A y)
  have hlip := locallyLipschitz_likelihoodRoot A hy
  have hm : bayesMarginal A h y = K.mass univ := by
    unfold bayesMarginal WeakPosteriorIdentity.marginal WeakH1Root.mass
    rw [Measure.restrict_univ]
    exact lintegral_congr (fun θ => by
      rw [show K.root θ = h.root θ * likelihoodRoot A y θ from
        WeakPosteriorIdentity.weakProductRoot_root P h _ hlip θ])
  have hs : K.mass (S y) =
      ∫⁻ θ in S y, ENNReal.ofReal (h.root θ ^ 2) * ENNReal.ofReal (likelihood A θ y) := by
    unfold WeakH1Root.mass
    apply lintegral_congr
    intro θ
    rw [show K.root θ = h.root θ * likelihoodRoot A y θ from
      WeakPosteriorIdentity.weakProductRoot_root P h _ hlip θ,
      mul_pow, ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    exact congrArg ENNReal.ofReal (Real.sq_sqrt (A.measurement.born_nonneg (copyState θ) hy))
  change bayesMarginal A h y * (WeakPosteriorIdentity.bayesRoot K).mass (S y) = _
  rw [hm, WeakPosteriorIdentity.bayesRoot, WeakPosteriorIdentity.mass_scaleRoot, ← mul_assoc]
  by_cases hz : K.mass univ = 0
  · have hzs : K.mass (S y) = 0 :=
      le_antisymm ((K.mass_mono (subset_univ _)).trans_eq hz) (zero_le _)
    rw [hz, zero_mul, zero_mul, ← hs, hzs]
  · rw [WeakPosteriorIdentity.marginal_mul_normalization_factor K hz, one_mul, hs]

theorem posteriorSuccess_eq_bornSuccess
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (h : WeakH1Root (2 * r * s)) (S : Y → Set (Parameter r s)) :
    H1PosteriorBound.posteriorSuccess A.measurement.reference (bayesMarginal A h)
      (posterior A P h) S = bornSuccess A h S :=
  lintegral_congr_ae (posterior_weighted_mass_eq_born_ae A P h S)

/-- The actual prior-times-Born joint density is jointly measurable. -/
theorem priorBorn_joint_aemeasurable (h : WeakH1Root (2 * r * s)) :
    AEMeasurable (fun z : Y × Parameter r s => ENNReal.ofReal (h.root z.2 ^ 2) *
      ENNReal.ofReal (likelihood A z.2 z.1)) (A.measurement.reference.prod volume) :=
  (h.root_aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal.comp_snd.mul
    (likelihood_joint_measurable A).aemeasurable.ennreal_ofReal

/-- Tonelli identifies the actual prior-average Born success probability with
the outcome-first Bayes integral. The measurable joint event is explicit;
no chi-squared-loss measurability is silently assumed. -/
theorem priorAverageSuccess_eq_bornSuccess
    (h : WeakH1Root (2 * r * s)) (S : Y → Set (Parameter r s))
    (hS : MeasurableSet {z : Y × Parameter r s | z.2 ∈ S z.1}) :
    priorAverageSuccess A h S = bornSuccess A h S := by
  let f : Y × Parameter r s → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (h.root z.2 ^ 2) * ENNReal.ofReal (likelihood A z.2 z.1)
  have hf : AEMeasurable f (A.measurement.reference.prod volume) := priorBorn_joint_aemeasurable A h
  have hleft : bornSuccess A h S =
      ∫⁻ y, (∫⁻ θ, ({z : Y × Parameter r s | z.2 ∈ S z.1}.indicator f) (y, θ))
        ∂A.measurement.reference := by
    apply lintegral_congr
    intro y
    have hSy : MeasurableSet (S y) := measurable_prodMk_left hS
    rw [← lintegral_indicator hSy]
    rfl
  have hright : priorAverageSuccess A h S =
      ∫⁻ θ, ∫⁻ y, ({z : Y × Parameter r s | z.2 ∈ S z.1}.indicator f) (y, θ)
        ∂A.measurement.reference := by
    apply lintegral_congr
    intro θ
    have hSθ : MeasurableSet {y | θ ∈ S y} := measurable_prodMk_right hS
    rw [A.outcomeMeasure_apply (state θ) hSθ]
    change ENNReal.ofReal (h.root θ ^ 2) *
      (∫⁻ y in {y | θ ∈ S y}, ENNReal.ofReal (likelihood A θ y) ∂A.measurement.reference) = _
    rw [← lintegral_const_mul'' _
      ((likelihood_measurable A θ).aemeasurable.ennreal_ofReal.restrict),
      ← lintegral_indicator hSθ]
    rfl
  rw [hleft, hright]
  exact (lintegral_lintegral_swap
    (f := fun (y : Y) (θ : Parameter r s) =>
      ({z : Y × Parameter r s | z.2 ∈ S z.1}.indicator f) (y, θ))
    (hf.indicator hS)).symm

/-- Corollary 3.3 for the actual collective graph experiment. All experiment
regularity, the actual posterior information identity and the Born/Bayes
success conversion have been proved in this file. The only classical external
inputs are the independently registered Sobolev and weak-derivative facts. -/
theorem priorAverageSuccess_bound
    (hp : 3 ≤ 2 * r * s)
    (hs : TalentiH1SharpInput (2 * r * s)) (hc : TalentiCoarseInput (2 * r * s))
    (P : WeakPosteriorIdentity.WeakLocallyLipschitzProductInput (2 * r * s))
    (U : WeakPosteriorIdentity.WeakDerivativeUniquenessInput (2 * r * s))
    (h : WeakH1Root (2 * r * s)) (S : Y → Set (Parameter r s)) {v : ℝ≥0∞}
    (hS : MeasurableSet {z : Y × Parameter r s | z.2 ∈ S z.1})
    (hv : ∀ᵐ y ∂A.measurement.reference, volume (S y) ≤ v) :
    priorAverageSuccess A h S ≤
      v ^ (2 / ((2 * r * s : ℕ) : ℝ)) / ((2 * r * s : ℕ) : ℝ≥0∞) *
        (h.fisher + WeakPosteriorIdentity.dataInformation A.measurement.reference h
          (likelihoodRoot A)) := by
  rw [priorAverageSuccess_eq_bornSuccess A h S hS, ← posteriorSuccess_eq_bornSuccess A P h S]
  apply H1PosteriorBound.posterior_success_bound_of_identity hp hs hc
    A.measurement.reference (bayesMarginal A h) (posterior A P h) S hv
  · exact WeakPosteriorIdentity.weightedPosteriorFisher_aemeasurable
      A.measurement.reference P U h (likelihoodRoot A) (locallyLipschitz_likelihoodRoot_ae A)
      (WeakPosteriorIdentity.weakProductDerivative_energy_aemeasurable
        A.measurement.reference h (likelihoodRoot A)
        (likelihoodRoot_joint_measurable A).aestronglyMeasurable
        (likelihoodRoot_fderiv_joint_measurable A).aestronglyMeasurable)
  · exact posterior_information_identity A P U h

/-- The learner's actual successful graph parameters, restricted to the
prior's parameter domain. No measurability of a spectral loss is asserted by
this definition. -/
def successParameters (loss : Density (StateIndex r s) → Density (StateIndex r s) → ℝ≥0∞)
    (ε : ℝ≥0∞) (T : Set (Parameter r s)) (y : Y) : Set (Parameter r s) :=
  {θ | θ ∈ T ∧ loss (state θ) (A.estimator.estimate y) ≤ ε}

/-- A genuine uniform rank-learning guarantee gives the Bayesian success
lower bound for every normalized prior supported in the stated parameter
domain. This uses the actual Born law and the graph family's proved rank. -/
theorem learnsRank_le_priorAverageSuccess
    (loss : Density (StateIndex r s) → Density (StateIndex r s) → ℝ≥0∞)
    (ε q : ℝ≥0∞) (h : WeakH1Root (2 * r * s)) (hh : h.mass univ = 1)
    (T : Set (Parameter r s)) (hT : ∀ θ ∉ T, h.root θ = 0)
    (hlearn : A.LearnsRank loss r ε q) :
    q ≤ priorAverageSuccess A h (successParameters A loss ε T) := by
  have hd : AEMeasurable (fun θ => ENNReal.ofReal (h.root θ ^ 2)) volume :=
    (h.root_aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hn : (∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2)) = 1 := by
    simpa only [WeakH1Root.mass, Measure.restrict_univ] using hh
  have hq : (∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) * q) = q := by
    have he : (fun θ : Parameter r s => ENNReal.ofReal (h.root θ ^ 2) * q) =
        fun θ => q * ENNReal.ofReal (h.root θ ^ 2) := funext (fun _ => mul_comm _ _)
    rw [he, lintegral_const_mul'' q hd, hn, mul_one]
  calc
    q = ∫⁻ θ, ENNReal.ofReal (h.root θ ^ 2) * q := hq.symm
    _ ≤ priorAverageSuccess A h (successParameters A loss ε T) := by
      apply lintegral_mono
      intro θ
      by_cases hθ : θ ∈ T
      · have he : {y | θ ∈ successParameters A loss ε T y} =
            A.successSet loss (state θ) ε := by
          ext y
          simp only [successParameters, mem_setOf_eq, hθ, true_and, CollectiveModel.Learner.successSet]
        change ENNReal.ofReal (h.root θ ^ 2) * q ≤
          ENNReal.ofReal (h.root θ ^ 2) * A.outcomeMeasure (state θ)
            {y | θ ∈ successParameters A loss ε T y}
        rw [he]
        exact mul_le_mul_left' (hlearn (state θ) (state_rank θ).le).2 _
      · simp only [hT θ hθ, zero_pow two_ne_zero, ENNReal.ofReal_zero, zero_mul]
        exact le_rfl

end Paper26.GraphExperiment
