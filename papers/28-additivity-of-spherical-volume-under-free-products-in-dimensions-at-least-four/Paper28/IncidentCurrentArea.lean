import Paper28.EuclideanAreaInput
import Paper28.ExteriorIncidentEnvelope

/-! The own finite-piece upper mass estimate. Generic AK smooth-lift
locality identifies each actual metric differential; choosing an incident
piece bounds it by the constructed actual exterior-Jacobian envelope. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory Set
open scoped Topology
universe w v

set_option maxHeartbeats 600000 in
theorem push_mass_le_incident_envelope {Y : Type w} (metricY : MetricSpace Y) {d k : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf)
    (A : EuclideanCurrentAreaInput metricY I R J U f hU hf P)
    (C : supportedCurrents I U k)
    {Idx : Type*} [Fintype Idx] (m : Idx → ℕ)
    (pieces : Idx → Set (EuclideanAmbient d))
    (D : ∀ j, EuclideanAmbient d → Matrix (Fin (m j)) (Fin d) ℝ)
    (hClosed : ∀ j, IsClosed (pieces j)) (hD : ∀ j, ContinuousOn (D j) (pieces j))
    (hLifts : ∀ j, ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), x ∈ pieces j →
      A.metricJacobian k C x = exteriorJacobian (k := k) (D j x) (R.polar C.val x))
    (hCover : I.support C.val ⊆ ⋃ j, pieces j)
    (B : Idx → ℝ) (hBound : ∀ j, ∀ x ∈ pieces j, ∀ τ : EuclideanExterior d k,
      ‖τ‖ = 1 → exteriorJacobian (k := k) (D j x) τ ≤ B j) :
    J.mass (P.push k C) ≤ ∫ p, exteriorIncidentEnvelope (k := k) m pieces D B p
      ∂(orientedTangentMeasure R C.val : Measure (EuclideanAmbient d × EuclideanExterior d k)) := by
  let env := exteriorIncidentEnvelope (k := k) m pieces D B
  have hEnv : UpperSemicontinuous env :=
    exteriorIncidentEnvelope_upperSemicontinuous (k := k) m pieces D B hClosed hD
  obtain ⟨M,hM⟩ := exteriorIncidentEnvelope_bounded (k := k) m pieces D B
  have hGraph : Measurable (fun x => (x,R.polar C.val x)) := measurable_id.prodMk (R.polar_measurable C.val)
  have hEnvMeas : Measurable env := hEnv.measurable
  have hInt : Integrable (fun x => env (x,R.polar C.val x)) (R.massMeasure C.val : Measure (EuclideanAmbient d)) := by
    apply (integrable_const M).mono' (hEnvMeas.comp hGraph).aestronglyMeasurable
    apply ae_of_all
    intro x
    rw [Real.norm_eq_abs]
    change |exteriorIncidentEnvelope (k := k) m pieces D B (x,R.polar C.val x)| ≤ M
    rw [abs_of_nonneg (hM (x,R.polar C.val x)).1]
    exact (hM _).2
  have hPoint : ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)),
      A.metricJacobian k C x ≤ env (x,R.polar C.val x) := by
    filter_upwards [ae_all_iff.mpr hLifts,R.polar_unit C.val,R.support_ae C.val] with x hx hτ hSupport
    obtain ⟨j,hj⟩ := mem_iUnion.mp (hCover hSupport)
    rw [hx j hj]
    have hClip := hBound j x hj (R.polar C.val x) hτ
    have hMax := le_incidentEnvelope (fun j => Prod.fst ⁻¹' pieces j)
      (fun j (p : EuclideanAmbient d × EuclideanExterior d k) =>
        min (B j) (exteriorJacobian (k := k) (D j p.1) p.2)) (x,R.polar C.val x) j hj
    change min (B j) (exteriorJacobian (k := k) (D j x) (R.polar C.val x)) ≤ env (x,R.polar C.val x) at hMax
    rw [min_eq_right hClip] at hMax
    exact hMax
  have hMass := (A.mass_area_le k C).trans (integral_mono_ae (A.jacobian_integrable k C) hInt hPoint)
  change J.mass (P.push k C) ≤ ∫ p, env p ∂Measure.map (fun x => (x,R.polar C.val x))
    (R.massMeasure C.val : Measure (EuclideanAmbient d))
  rw [integral_map hGraph.aemeasurable hEnvMeas.aestronglyMeasurable]
  exact hMass

end Paper28
