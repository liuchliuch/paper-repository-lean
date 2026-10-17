import Paper26.FisherPullback
import Paper26.GraphExperiment

/-!
# Actual graph likelihood Fisher budget

The sole graph-geometry input below describes actual states and actual matrix
entry derivatives by an ambient unitary and a real Euclidean contraction. It
contains no score, Fisher, probability, or success bound. The likelihood and
root derivatives are those already defined in `GraphExperiment`.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory Paper26.QuantumModel Paper26.ContinuousPOVM

namespace Paper26.GraphFisherBudget

open AlignedFisherBudget FisherPullback

/-- The standard graph tangent-coordinate identity, NZ §4.2.3 / P26 (27).
This known geometry input retains every parameter and every actual matrix
entry derivative. Its only quantitative assertion is that the actual real
coordinate change is a contraction. No information bound is a field. -/
structure GraphTangentInput : Prop where
  geometry : ∀ (r s : ℕ) [NeZero r] (θ : ParameterSpace r s),
    ∃ (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ)
      (T : ParameterSpace r s →L[ℝ] ParameterSpace r s),
      ‖T‖ ≤ 1 ∧
      GraphExperiment.state θ = PositiveLossBridge.conjugateDensity W
        (GraphFamily.density (0 : Matrix (Fin s) (Fin r) ℂ)) ∧
      ∀ (i j : Fin r ⊕ Fin s) (v : ParameterSpace r s),
        fderiv ℝ (fun t : ParameterSpace r s => (GraphExperiment.state t).matrix i j) θ v =
          ((W : EffectMatrix r s) *
            tangent ((MatrixCoordinates.coordinates r s).symm (T v)) *
              (W : EffectMatrix r s)ᴴ) i j

section SingleCopyReindex
variable {ι Y : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Y]

/-- Actual one-copy tensor coordinates are identified by evaluation on `Fin 1`. -/
def oneCopyEquiv : ι ≃ (Fin 1 → ι) := (Equiv.funUnique (Fin 1) ι).symm

variable (M : DominatedPOVM (Fin 1 → ι) Y)

def oneCopyPOVM : DominatedPOVM ι Y where
  reference := M.reference
  reference_finite := M.reference_finite
  effect y := (M.effect y).submatrix oneCopyEquiv oneCopyEquiv
  entry_measurable i j := M.entry_measurable _ _
  positive_ae := M.positive_ae.mono fun _ hy => hy.submatrix _
  entry_integrable i j := M.entry_integrable _ _
  total i j := by
    simpa only [Matrix.one_apply, (oneCopyEquiv (ι := ι)).injective.eq_iff] using
      M.total (oneCopyEquiv i) (oneCopyEquiv j)

@[simp] theorem oneCopyPOVM_reference : (oneCopyPOVM M).reference = M.reference := rfl

theorem oneCopyPOVM_born (ρ : Density ι) (y : Y) :
    (oneCopyPOVM M).born ρ y = M.born (TensorCopies.density ρ 1) y := by
  unfold DominatedPOVM.born
  rw [DominatedPOVM.complexBorn_eq_sum, DominatedPOVM.complexBorn_eq_sum]
  apply congrArg Complex.re
  exact Fintype.sum_equiv oneCopyEquiv _ _ fun i =>
    Fintype.sum_equiv oneCopyEquiv _ _ fun j => by
      simp [oneCopyPOVM, TensorCopies.density_matrix, oneCopyEquiv]

end SingleCopyReindex

section ActualLikelihood
variable {r s : ℕ} [NeZero r]
variable {Y : Type*} [MeasurableSpace Y]
variable (A : CollectiveModel.Learner (Fin r ⊕ Fin s) Y 1)

abbrev ambientPOVM := oneCopyPOVM A.measurement

theorem likelihood_eq_ambient (θ : ParameterSpace r s) (y : Y) :
    GraphExperiment.likelihood A θ y = (ambientPOVM A).born (GraphExperiment.state θ) y :=
  (oneCopyPOVM_born A.measurement _ y).symm

/-- Native differentiation of the actual one-copy Born trace. -/
theorem ambient_hasFDerivAt (θ : ParameterSpace r s) (y : Y) :
    HasFDerivAt (fun t : ParameterSpace r s =>
      (ambientPOVM A).born (GraphExperiment.state t) y)
      (Complex.reCLM.comp (∑ i : Fin r ⊕ Fin s, ∑ j : Fin r ⊕ Fin s,
        (ambientPOVM A).effect y j i •
          fderiv ℝ (fun t : ParameterSpace r s => (GraphExperiment.state t).matrix i j) θ)) θ := by
  simp_rw [DominatedPOVM.born, DominatedPOVM.complexBorn_eq_sum]
  exact Complex.reCLM.hasFDerivAt.comp θ (HasFDerivAt.fun_sum (fun i _ =>
    HasFDerivAt.fun_sum (fun j _ =>
      ((GraphExperiment.contDiff_state_entry (k := 1) i j).differentiable_one θ).hasFDerivAt.mul_const _)))

theorem likelihoodDerivative_eq_ambient (θ : ParameterSpace r s) (y : Y) :
    GraphExperiment.likelihoodDerivative A θ y =
      Complex.reCLM.comp (∑ i : Fin r ⊕ Fin s, ∑ j : Fin r ⊕ Fin s,
        (ambientPOVM A).effect y j i •
          fderiv ℝ (fun t : ParameterSpace r s => (GraphExperiment.state t).matrix i j) θ) := by
  have h := ambient_hasFDerivAt A θ y
  simp_rw [← likelihood_eq_ambient A] at h
  exact (GraphExperiment.likelihood_hasFDerivAt A θ y).unique h

/-- The raw matrix tangent identity determines the actual likelihood
functional, rather than supplying a score identity as an input. -/
theorem likelihoodDerivative_eq_contracted (θ : ParameterSpace r s)
    (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ)
    (T : ParameterSpace r s →L[ℝ] ParameterSpace r s)
    (hd : ∀ (i j : Fin r ⊕ Fin s) (v : ParameterSpace r s),
      fderiv ℝ (fun t : ParameterSpace r s => (GraphExperiment.state t).matrix i j) θ v =
        ((W : EffectMatrix r s) * tangent ((MatrixCoordinates.coordinates r s).symm (T v)) *
          (W : EffectMatrix r s)ᴴ) i j) (y : Y) :
    GraphExperiment.likelihoodDerivative A θ y =
      (score r s (conjugatedEffect W ((ambientPOVM A).effect y))).comp T := by
  rw [likelihoodDerivative_eq_ambient]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, Complex.reCLM_apply, hd]
  rw [transported_directionalDerivative r s T W]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, smul_eq_mul, mul_comm]

theorem likelihood_eq_transported_probability (θ : ParameterSpace r s)
    (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ)
    (hρ : GraphExperiment.state θ = PositiveLossBridge.conjugateDensity W
      (GraphFamily.density (0 : Matrix (Fin s) (Fin r) ℂ))) (y : Y) :
    GraphExperiment.likelihood A θ y =
      probability (conjugatedEffect W ((ambientPOVM A).effect y)) := by
  rw [likelihood_eq_ambient, hρ, ← unitaryPOVM_born, ← probability_eq_born]
  rfl

/-- Actual square-root derivative energy equals the contracted Fisher
contribution, including the zero-likelihood branch. -/
theorem root_energy_eq_contracted (θ : ParameterSpace r s)
    (W : Matrix.unitaryGroup (Fin r ⊕ Fin s) ℂ)
    (T : ParameterSpace r s →L[ℝ] ParameterSpace r s)
    (hρ : GraphExperiment.state θ = PositiveLossBridge.conjugateDensity W
      (GraphFamily.density (0 : Matrix (Fin s) (Fin r) ℂ)))
    (hd : ∀ (i j : Fin r ⊕ Fin s) (v : ParameterSpace r s),
      fderiv ℝ (fun t : ParameterSpace r s => (GraphExperiment.state t).matrix i j) θ v =
        ((W : EffectMatrix r s) * tangent ((MatrixCoordinates.coordinates r s).symm (T v)) *
          (W : EffectMatrix r s)ᴴ) i j) (y : Y)
    (hy : ((ambientPOVM A).effect y).PosSemidef) :
    4 * ‖fderiv ℝ (GraphExperiment.likelihoodRoot A y) θ‖ ^ 2 =
      contractedFisher r s (conjugatedEffect W ((ambientPOVM A).effect y)) T := by
  have hp := likelihood_eq_transported_probability A θ W hρ y
  have hD := likelihoodDerivative_eq_contracted A θ W T hd y
  rw [GraphExperiment.likelihoodRoot_fderiv, hD]
  unfold contractedFisher
  by_cases hz : probability (conjugatedEffect W ((ambientPOVM A).effect y)) = 0
  · rw [if_pos hz]
    simp only [GraphExperiment.likelihoodRoot, hp, hz, Real.sqrt_zero, mul_zero,
      div_zero, zero_smul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]
  · rw [if_neg hz]
    have hp0 : 0 ≤ probability (conjugatedEffect W ((ambientPOVM A).effect y)) :=
      probability_nonneg _ (conjugatedEffect_posSemidef W _ hy)
    simp only [GraphExperiment.likelihoodRoot, hp, norm_smul, Real.norm_eq_abs, mul_pow,
      sq_abs, div_pow]
    rw [Real.sq_sqrt hp0]
    field_simp
    ring

theorem root_energy_integrable (G : GraphTangentInput) (θ : ParameterSpace r s) :
    Integrable (fun y => 4 * ‖fderiv ℝ (GraphExperiment.likelihoodRoot A y) θ‖ ^ 2)
      A.measurement.reference := by
  obtain ⟨W, T, hT, hρ, hd⟩ := G.geometry r s θ
  have hI := FisherPullback.integrable_contractedFisher r s
    (unitaryPOVM (ambientPOVM A) W) T hT
  apply hI.congr
  filter_upwards [A.measurement.positive_ae] with y hy
  exact (root_energy_eq_contracted A θ W T hρ hd y (hy.submatrix _)).symm

/-- Actual one-copy root-gradient Fisher budget, on arbitrary measurable
outcome spaces, derived from the graph tangent geometry and native effect
bounds. In particular no information bound occurs in `GraphTangentInput`. -/
theorem onecopy_fisher_budget (G : GraphTangentInput) (θ : ParameterSpace r s) :
    ∫ y, 4 * ‖fderiv ℝ (GraphExperiment.likelihoodRoot A y) θ‖ ^ 2
      ∂A.measurement.reference ≤ 4 * (s : ℝ) / (r : ℝ) := by
  obtain ⟨W, T, hT, hρ, hd⟩ := G.geometry r s θ
  calc
    _ = ∫ y, contractedFisher r s (conjugatedEffect W ((ambientPOVM A).effect y)) T
        ∂A.measurement.reference := by
      apply integral_congr_ae
      filter_upwards [A.measurement.positive_ae] with y hy
      exact root_energy_eq_contracted A θ W T hρ hd y (hy.submatrix _)
    _ ≤ _ := unitary_contracted_fisher_budget r s (ambientPOVM A) T W hT

/-- The same quantitative budget in the root-energy normalization used by
`GraphExperiment.localEnergy_of_uniform_bound`. -/
theorem onecopy_root_energy_budget (G : GraphTangentInput) (θ : ParameterSpace r s) :
    ∫ y, ‖fderiv ℝ (GraphExperiment.likelihoodRoot A y) θ‖ ^ 2
      ∂A.measurement.reference ≤ (s : ℝ) / (r : ℝ) := by
  have h := onecopy_fisher_budget A G θ
  rw [integral_const_mul, mul_div_assoc] at h
  linarith

theorem onecopy_fisher_budget_lintegral (G : GraphTangentInput) (θ : ParameterSpace r s) :
    ∫⁻ y, ENNReal.ofReal (4 * ‖fderiv ℝ (GraphExperiment.likelihoodRoot A y) θ‖ ^ 2)
      ∂A.measurement.reference ≤ ENNReal.ofReal (4 * (s : ℝ) / (r : ℝ)) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (root_energy_integrable A G θ)
    (Filter.Eventually.of_forall fun y => by positivity)]
  exact ENNReal.ofReal_le_ofReal (onecopy_fisher_budget A G θ)

end ActualLikelihood
end Paper26.GraphFisherBudget
