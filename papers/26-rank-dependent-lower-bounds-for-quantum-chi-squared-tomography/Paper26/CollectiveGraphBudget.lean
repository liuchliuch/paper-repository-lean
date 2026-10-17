import Paper26.GraphFisherBudget
import Paper26.FlatSLD
import Paper26.TensorSLD

/-!
# Native collective graph-family Fisher budget

The sole graph input is the actual state/tangent geometry
`GraphFisherBudget.GraphTangentInput`.  Finite product differentiation
identifies the actual tensor-state derivative with `TensorSLD.derivativeCopy`.
Explicit transported flat SLDs, native tensor energy additivity, and native
weighted trace Cauchy--Schwarz give the arbitrary-outcome collective bound.
No measured-Fisher or collective-budget assertion is an external field.
-/

noncomputable section
open scoped BigOperators Matrix ComplexOrder ENNReal
open MeasureTheory

namespace Paper26.CollectiveGraphBudget

open QuantumModel ContinuousPOVM GraphExperiment WeightedTraceCS

variable {r s n : ℕ} [NeZero r]
variable {Y : Type*} [MeasurableSpace Y]

/-- The actual single-copy matrix-entry Fréchet derivative in a real direction. -/
def stateDerivative (θ v : Parameter r s) : Matrix (StateIndex r s) (StateIndex r s) ℂ :=
  fun i j => fderiv ℝ (fun t : Parameter r s => (state t).matrix i j) θ v

/-- Native finite product rule on the actual tensor matrix entries, including `n=0`. -/
theorem copyEntry_fderiv (θ v : Parameter r s) (i j : CopyIndex r s n) :
    fderiv ℝ (fun t : Parameter r s => (copyState t).matrix i j) θ v =
      TensorSLD.derivativeCopy (state θ) (stateDerivative θ v) n i j := by
  change fderiv ℝ (fun t : Parameter r s =>
    ∏ k : Fin n, (state t).matrix (i k) (j k)) θ v = _
  rw [fderiv_finset_prod (fun k _ =>
    (contDiff_state_entry (k := 1) (i k) (j k)).differentiable_one θ)]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    TensorSLD.derivativeCopy, Matrix.sum_apply, TensorSLD.slot_apply, stateDerivative,
    smul_eq_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

variable (A : CollectiveModel.Learner (StateIndex r s) Y n)

/-- The actual likelihood functional differentiates the true tensor-copy matrix. -/
theorem likelihoodDerivative_direction (θ v : Parameter r s) (y : Y) :
    likelihoodDerivative A θ y v = derivative A.measurement
      (TensorSLD.derivativeCopy (state θ) (stateDerivative θ v) n) y := by
  simp only [likelihoodDerivative, complexLikelihoodDerivative, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Complex.reCLM_apply,
    copyEntry_fderiv]
  simp only [derivative, TailConvexity.pairing, Matrix.trace, Matrix.diag_apply,
    Matrix.mul_apply, smul_eq_mul, mul_comm]

lemma likelihood_eq_copyBorn (θ : Parameter r s) (y : Y) :
    likelihood A θ y = A.measurement.born (copyState θ) y := rfl

/-- Actual classical directional information in each real orthonormal coordinate. -/
def coordinateInfo (θ : Parameter r s) (i : Fin (2 * r * s)) (y : Y) : ℝ :=
  if likelihood A θ y = 0 then 0 else
    (likelihoodDerivative A θ y (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i)) ^ 2 /
      likelihood A θ y

/-- No score field is assumed: the coordinate information is exactly the actual
matrix-tangent Fisher integrand already controlled by weighted trace CS. -/
theorem coordinateInfo_eq_fisherDensity (θ : Parameter r s) (i : Fin (2 * r * s)) :
    coordinateInfo A θ i = fisherDensity A.measurement (copyState θ)
      (TensorSLD.derivativeCopy (state θ)
        (stateDerivative θ (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i)) n) := by
  funext y
  simp only [coordinateInfo, fisherDensity, likelihood_eq_copyBorn,
    likelihoodDerivative_direction]

/-- The actual root-gradient square is the sum of actual coordinate Fisher
contributions, including the zero-likelihood case. -/
theorem root_energy_eq_sum (θ : Parameter r s) {y : Y}
    (hy : (A.measurement.effect y).PosSemidef) :
    4 * ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ 2 = ∑ i, coordinateInfo A θ i y := by
  have hp : 0 ≤ likelihood A θ y := A.measurement.born_nonneg (copyState θ) hy
  by_cases hz : likelihood A θ y = 0
  · simp only [likelihoodRoot_fderiv, likelihoodRoot, hz, Real.sqrt_zero, mul_zero,
      div_zero, zero_smul, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero, coordinateInfo, if_pos, Finset.sum_const_zero]
  · have hp' : 0 < likelihood A θ y := lt_of_le_of_ne hp (Ne.symm hz)
    have hsqrt : Real.sqrt (likelihood A θ y) ≠ 0 := (Real.sqrt_pos.mpr hp').ne'
    calc
      _ = ∑ i : Fin (2 * r * s),
          4 * (fderiv ℝ (likelihoodRoot A y) θ
            (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i)) ^ 2 := by
        rw [← WeakPosteriorIdentity.dualEnergy_eq_norm_sq]
        simp only [WeakPosteriorIdentity.dualEnergy, Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        rw [likelihoodRoot_fderiv]
        simp only [coordinateInfo, if_neg hz, ContinuousLinearMap.smul_apply,
          smul_eq_mul, likelihoodRoot]
        field_simp
        rw [Real.sq_sqrt hp]
        ring

/-- Recovering the actual symmetric tangent from its explicit SLD equation. -/
lemma sldTangent_of_equation {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ H D : Matrix ι ι ℂ) (h : ρ * H + H * ρ = (2 : ℂ) • D) :
    sldTangent ρ H = D := by
  rw [sldTangent, h]
  ext i j
  simp only [Matrix.smul_apply, smul_eq_mul, Complex.real_smul]
  norm_num
  ring

/-- Every actual graph parameter has a complete family of actual collective
SLDs, with total energy at most `8*n*s`.  Only the raw graph geometry is used. -/
theorem exists_collective_slds (G : GraphFisherBudget.GraphTangentInput) (θ : Parameter r s) :
    ∃ H : Fin (2 * r * s) → Matrix (CopyIndex r s n) (CopyIndex r s n) ℂ,
      (∀ i, (H i).IsHermitian) ∧
      (∀ i, sldTangent (copyState θ).matrix (H i) =
        TensorSLD.derivativeCopy (state θ)
          (stateDerivative θ (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i)) n) ∧
      (∑ i, (Matrix.trace ((copyState θ).matrix * (H i * H i))).re) ≤
        8 * (n : ℝ) * s := by
  obtain ⟨W, T, hT, hρ, hd⟩ := G.geometry r s θ
  change state θ = FlatSLD.rotateState W at hρ
  let K := FlatSLD.contractedDirection r s T
  let H₁ := fun i => FlatSLD.rotateSLD W (K i)
  let H := fun i => TensorSLD.totalLift (H₁ i) n
  have hD (i : Fin (2 * r * s)) :
      stateDerivative θ (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i) =
        FlatSLD.rotateTangent W (K i) := by
    ext a b
    exact hd a b _
  have hHerm (i : Fin (2 * r * s)) : (H₁ i).IsHermitian :=
    FlatSLD.rotateSLD_hermitian W (K i)
  have hzero (i : Fin (2 * r * s)) : (Matrix.trace ((state θ).matrix * H₁ i)).re = 0 := by
    rw [hρ]
    exact FlatSLD.rotateSLD_mean_zero W (K i)
  have hEq (i : Fin (2 * r * s)) :
      (state θ).matrix * H₁ i + H₁ i * (state θ).matrix =
        (2 : ℂ) • stateDerivative θ (EuclideanSpace.basisFun (Fin (2 * r * s)) ℝ i) := by
    rw [hρ, hD]
    exact FlatSLD.rotateSLD_equation W (K i)
  refine ⟨H, (fun i => TensorSLD.totalLift_hermitian _ (hHerm i) n), ?_, ?_⟩
  · intro i
    exact sldTangent_of_equation _ _ _ (TensorSLD.sld_equation _ _ _ (hEq i) n)
  · calc
      _ = (n : ℝ) * ∑ i, (Matrix.trace ((state θ).matrix * (H₁ i * H₁ i))).re := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [H, copyState, pow_two] using
          TensorSLD.totalLift_energy (state θ) (H₁ i) (hHerm i) (hzero i) n
      _ ≤ (n : ℝ) * (8 * s) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg n)
        rw [hρ]
        exact FlatSLD.rotate_contraction_energy_sum_le r s W T hT
      _ = _ := by ring

/-- The actual root-gradient energy is integrable, so the real-integral budget
cannot hold merely because a nonintegrable integral was totalized to zero. -/
theorem root_energy_integrable (G : GraphFisherBudget.GraphTangentInput) (θ : Parameter r s) :
    Integrable (fun y => 4 * ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ 2)
      A.measurement.reference := by
  obtain ⟨H, hH, hD, _⟩ := exists_collective_slds (n := n) G θ
  have hi (i : Fin (2 * r * s)) : Integrable (coordinateInfo A θ i) A.measurement.reference := by
    rw [coordinateInfo_eq_fisherDensity, ← hD i]
    exact fisherDensity_sld_integrable A.measurement (copyState θ) (H i) (hH i)
  apply (integrable_finset_sum Finset.univ (fun i _ => hi i)).congr
  exact A.measurement.positive_ae.mono (fun _ hy => (root_energy_eq_sum A θ hy).symm)

/-- Collective Lemma 3.5's actual likelihood-root Fisher budget, derived from
raw graph geometry, actual tensor products, and native matrix inequalities. -/
theorem collective_fisher_budget (G : GraphFisherBudget.GraphTangentInput) (θ : Parameter r s) :
    (∫ y, 4 * ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ 2 ∂A.measurement.reference) ≤
      8 * (n : ℝ) * s := by
  obtain ⟨H, hH, hD, hsum⟩ := exists_collective_slds (n := n) G θ
  have hi (i : Fin (2 * r * s)) : Integrable (coordinateInfo A θ i) A.measurement.reference := by
    rw [coordinateInfo_eq_fisherDensity, ← hD i]
    exact fisherDensity_sld_integrable A.measurement (copyState θ) (H i) (hH i)
  calc
    _ = ∫ y, ∑ i : Fin (2 * r * s), coordinateInfo A θ i y ∂A.measurement.reference := by
      apply integral_congr_ae
      exact A.measurement.positive_ae.mono (fun _ hy => root_energy_eq_sum A θ hy)
    _ = ∑ i : Fin (2 * r * s), ∫ y, coordinateInfo A θ i y ∂A.measurement.reference :=
      integral_finset_sum _ (fun i _ => hi i)
    _ ≤ ∑ i : Fin (2 * r * s), (Matrix.trace ((copyState θ).matrix * (H i * H i))).re := by
      apply Finset.sum_le_sum
      intro i _
      rw [coordinateInfo_eq_fisherDensity, ← hD i]
      exact integral_fisherDensity_sld_le A.measurement (copyState θ) (H i) (hH i)
    _ ≤ _ := hsum

/-- The actual nonnegative-integral form used by weak posterior energy bounds. -/
theorem collective_fisher_budget_lintegral (G : GraphFisherBudget.GraphTangentInput)
    (θ : Parameter r s) :
    (∫⁻ y, ENNReal.ofReal (4 * ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ 2)
      ∂A.measurement.reference) ≤ ENNReal.ofReal (8 * (n : ℝ) * s) := by
  rw [← ofReal_integral_eq_lintegral_ofReal (root_energy_integrable A G θ)
    (Filter.Eventually.of_forall fun y => by positivity)]
  exact ENNReal.ofReal_le_ofReal (collective_fisher_budget A G θ)

/-- The unscaled root-gradient energy bound, with factor four removed internally. -/
theorem collective_root_energy_budget (G : GraphFisherBudget.GraphTangentInput)
    (θ : Parameter r s) :
    (∫ y, ‖fderiv ℝ (likelihoodRoot A y) θ‖ ^ 2 ∂A.measurement.reference) ≤
      2 * (n : ℝ) * s := by
  have h := collective_fisher_budget A G θ
  rw [integral_const_mul] at h
  linarith

end Paper26.CollectiveGraphBudget
