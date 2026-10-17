import Paper38.GaussianDifferentiation
import Paper38.GaussianSecondDerivativeRules
import Paper38.LogDetGeometry
import Paper38.HilbertCoordinates

/-! Complete actual Gaussian energy variations and intrinsic source geometry. -/
noncomputable section
set_option maxHeartbeats 800000

open MeasureTheory ProbabilityTheory Set Topology
open scoped BigOperators ENNReal Matrix Matrix.Norms.Frobenius

namespace Paper38.GaussianEnergyGeometry
open Paper38.Model Paper38.GaussianDifferentiation


variable {d : ℕ} {V : E d → ℝ} {α β : ℝ}

lemma model_energy_eq (V : E d → ℝ) : Model.energy V =
    (fun q : Coordinates d => potentialAverage V q + LogDetGeometry.negLogDet q.2) := by
  funext q
  simp only [Model.energy, potentialAverage, evaluation_apply, LogDetGeometry.negLogDet, sub_eq_add_neg]

lemma model_energy_contDiffAt (hV : AdmissiblePotential V α β) (q : Coordinates d)
    (hq : q.2.det ≠ 0) : ContDiffAt ℝ 2 (Model.energy V) q := by
  rw [model_energy_eq]
  exact (potentialAverage_contDiff hV).contDiffAt.add
    ((LogDetGeometry.negLogDet_contDiffAt hq).comp q
      (ContinuousLinearMap.snd ℝ (E d) (Mat d)).contDiff.contDiffAt)

lemma model_energy_hasFDerivAt (hV : AdmissiblePotential V α β) (q : Coordinates d)
    (hq : q.2.det ≠ 0) :
    HasFDerivAt (Model.energy V)
      ((∫ z, integrandDifferential V q z ∂standardGaussian d) +
        (LogDetGeometry.negLogDetDifferential q.2).comp
          (ContinuousLinearMap.snd ℝ (E d) (Mat d))) q := by
  rw [model_energy_eq]
  have hlog : HasFDerivAt (fun p : Coordinates d => LogDetGeometry.negLogDet p.2)
      ((LogDetGeometry.negLogDetDifferential q.2).comp
        (ContinuousLinearMap.snd ℝ (E d) (Mat d))) q :=
    (LogDetGeometry.negLogDet_hasFDerivAt hq).comp q
      (ContinuousLinearMap.snd ℝ (E d) (Mat d)).hasFDerivAt
  exact (potentialAverage_hasFDerivAt hV q).add hlog

lemma model_energy_first_variation (hV : AdmissiblePotential V α β) (q w : Coordinates d)
    (hq : q.2.det ≠ 0) :
    fderiv ℝ (Model.energy V) q w =
      (∫ z, (fderiv ℝ V (q.1 + matVec q.2 z)) (w.1 + matVec w.2 z) ∂standardGaussian d) -
        Matrix.trace (q.2⁻¹ * w.2) := by
  rw [(model_energy_hasFDerivAt hV q hq).fderiv, ContinuousLinearMap.add_apply,
    ← potentialAverage_fderiv hV q, potentialAverage_first_variation hV q w]
  simp only [ContinuousLinearMap.comp_apply,
    LogDetGeometry.negLogDetDifferential_apply, sub_eq_add_neg] <;> rfl

lemma model_energy_second_variation (hV : AdmissiblePotential V α β) (q w : Coordinates d)
    (hq : q.2.det ≠ 0) :
    fderiv ℝ (fderiv ℝ (Model.energy V)) q w w =
      (∫ z, (fderiv ℝ (fderiv ℝ V) (q.1 + matVec q.2 z)
        (w.1 + matVec w.2 z)) (w.1 + matVec w.2 z) ∂standardGaussian d) +
        Matrix.trace (q.2⁻¹ * w.2 * q.2⁻¹ * w.2) := by
  have hlog : ContDiffAt ℝ 2 (fun p : Coordinates d => LogDetGeometry.negLogDet p.2) q :=
    (LogDetGeometry.negLogDet_contDiffAt hq).comp q
      (ContinuousLinearMap.snd ℝ (E d) (Mat d)).contDiff.contDiffAt
  rw [model_energy_eq, second_fderiv_add _ _ q w w (potentialAverage_contDiff hV).contDiffAt hlog,
    potentialAverage_second_variation hV]
  have hc := second_fderiv_comp_clm LogDetGeometry.negLogDet
    (ContinuousLinearMap.snd ℝ (E d) (Mat d)) q w w (LogDetGeometry.negLogDet_contDiffAt hq)
  change fderiv ℝ (fderiv ℝ (fun p : Coordinates d => LogDetGeometry.negLogDet p.2)) q w w =
    fderiv ℝ (fderiv ℝ LogDetGeometry.negLogDet) q.2 w.2 w.2 at hc
  rw [hc, LogDetGeometry.negLogDet_fderiv_second_of_det_ne_zero hq]

/-- The source energy is C² on its intrinsic positive-definite Hilbert domain. -/
lemma intrinsic_energy_contDiffOn (hV : AdmissiblePotential V α β) :
    ContDiffOn ℝ 2 (HilbertCoordinates.energy V) (HilbertCoordinates.Domain d) := by
  intro q hq
  change (HilbertCoordinates.toModel d q).2.PosDef at hq
  exact ((model_energy_contDiffAt hV (HilbertCoordinates.toModel d q) hq.det_pos.ne').comp q
    (HilbertCoordinates.toModel d).contDiff.contDiffAt).contDiffWithinAt

/-- Equation (4.7), with its exact Gaussian integral and log-determinant trace. -/
lemma intrinsic_energy_second_variation (hV : AdmissiblePotential V α β)
    (q v : HilbertCoordinates.Tangent d) (hq : q ∈ HilbertCoordinates.Domain d) :
    fderiv ℝ (fderiv ℝ (HilbertCoordinates.energy V)) q v v =
      (∫ z, GaussianEnergy.quadraticVariation V
        (HilbertCoordinates.toModel d q).1 (HilbertCoordinates.toModel d v).1
        (HilbertCoordinates.toModel d q).2 (HilbertCoordinates.toModel d v).2 z ∂standardGaussian d) +
      Matrix.trace ((HilbertCoordinates.toModel d q).2⁻¹ * (HilbertCoordinates.toModel d v).2 *
        (HilbertCoordinates.toModel d q).2⁻¹ * (HilbertCoordinates.toModel d v).2) := by
  change (HilbertCoordinates.toModel d q).2.PosDef at hq
  rw [show HilbertCoordinates.energy V = (fun p => Model.energy V (HilbertCoordinates.toModel d p)) from rfl]
  rw [second_fderiv_comp_clm (Model.energy V) (HilbertCoordinates.toModel d) q v v
    (model_energy_contDiffAt hV (HilbertCoordinates.toModel d q) hq.det_pos.ne')]
  exact model_energy_second_variation hV _ _ hq.det_pos.ne'

/-- The exact source α-strong Hessian lower bound in the Euclidean--Frobenius norm. -/
lemma intrinsic_energy_second_fderiv_lower (hV : AdmissiblePotential V α β)
    (q v : HilbertCoordinates.Tangent d) (hq : q ∈ HilbertCoordinates.Domain d) :
    α * ‖v‖ ^ 2 ≤ fderiv ℝ (fderiv ℝ (HilbertCoordinates.energy V)) q v v := by
  rw [intrinsic_energy_second_variation hV q v hq]
  have hpot := (GaussianEnergy.quadraticVariation_integral_bounds hV
    (HilbertCoordinates.toModel d q).1 (HilbertCoordinates.toModel d v).1
    (HilbertCoordinates.toModel d q).2 (HilbertCoordinates.toModel d v).2).1
  have htrace := LogDetGeometry.second_variation_nonneg hq
    (HilbertCoordinates.toModel_symmetric v)
  have hnorm : ‖(HilbertCoordinates.toModel d v).1‖ ^ 2 +
      frobSq (HilbertCoordinates.toModel d v).2 = ‖v‖ ^ 2 := by
    have hn := HilbertCoordinates.norm_ambient_sq (HilbertCoordinates.toModel d v)
    rw [HilbertCoordinates.ambient_toModel] at hn
    exact hn.symm
  rw [hnorm] at hpot
  linarith

end Paper38.GaussianEnergyGeometry
