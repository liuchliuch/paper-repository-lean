import Paper28.IncidentCurrentArea
import Paper28.PushforwardHomology
import Paper28.WeakMeasureInputs

/-! Own sharp mass continuity for finite smooth round lifts. At the limit
all incident metric Jacobians coincide a.e.; the constructed maximum has
that exact value. Portmanteau gives the sharp upper bound and actual pushed
fillings with vanishing mass give the reverse bound by generic AK LSC. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory Set
open scoped Topology
universe w v
variable {Y : Type w} (metricY : MetricSpace Y) {d k : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf)
    (A : EuclideanCurrentAreaInput metricY I R J U f hU hf P)

theorem incident_envelope_eq_metricJacobian_ae
    (C : supportedCurrents I U k) {Idx : Type*} [Fintype Idx] (m : Idx → ℕ)
    (pieces : Idx → Set (EuclideanAmbient d))
    (D : ∀ j, EuclideanAmbient d → Matrix (Fin (m j)) (Fin d) ℝ)
    (B : Idx → ℝ)
    (hLifts : ∀ j, ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), x ∈ pieces j →
      A.metricJacobian k C x = exteriorJacobian (k := k) (D j x) (R.polar C.val x))
    (hCover : I.support C.val ⊆ ⋃ j, pieces j)
    (hBound : ∀ j, ∀ x ∈ pieces j, ∀ τ : EuclideanExterior d k,
      ‖τ‖ = 1 → exteriorJacobian (k := k) (D j x) τ ≤ B j) :
    ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)),
      exteriorIncidentEnvelope (k := k) m pieces D B (x,R.polar C.val x) = A.metricJacobian k C x := by
  filter_upwards [ae_all_iff.mpr hLifts,R.polar_unit C.val,R.support_ae C.val] with x hx hτ hSupport
  apply incidentEnvelope_eq
  · exact A.jacobian_nonneg k C x
  · obtain ⟨j,hj⟩ := mem_iUnion.mp (hCover hSupport)
    exact ⟨j,hj⟩
  · intro j hj
    change min (B j) (exteriorJacobian (k := k) (D j x) (R.polar C.val x)) = A.metricJacobian k C x
    rw [min_eq_right (hBound j x hj _ hτ)]
    exact (hx j hj).symm

set_option maxHeartbeats 600000 in
theorem sharp_push_mass_upper (hPort : UpperPortmanteauInput.{0})
    (T : supportedCurrents I U k) (Qi : ℕ → supportedCurrents I U k)
    {Idx : Type*} [Fintype Idx] (m : Idx → ℕ) (pieces : Idx → Set (EuclideanAmbient d))
    (D : ∀ j, EuclideanAmbient d → Matrix (Fin (m j)) (Fin d) ℝ)
    (hK : ∀ j, IsCompact (pieces j)) (hD : ∀ j, ContinuousOn (D j) (pieces j))
    (hLifts : ∀ C : supportedCurrents I U k, ∀ j,
      ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), x ∈ pieces j →
        A.metricJacobian k C x = exteriorJacobian (k := k) (D j x) (R.polar C.val x))
    (hT : I.support T.val ⊆ ⋃ j, pieces j) (hQi : ∀ i, I.support (Qi i).val ⊆ ⋃ j, pieces j)
    (hInjective : Set.InjOn f (I.support T.val))
    (hWeak : Tendsto (fun i => orientedTangentMeasure R (Qi i).val) atTop (𝓝 (orientedTangentMeasure R T.val))) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop, J.mass (P.push k (Qi i)) ≤ J.mass (P.push k T)+ε := by
  choose B hB hBound using fun j => exists_exteriorJacobian_bound (k := k) (pieces j) (hK j) (D j) (hD j)
  let env := exteriorIncidentEnvelope (k := k) m pieces D B
  have hEnv : UpperSemicontinuous env :=
    exteriorIncidentEnvelope_upperSemicontinuous (k := k) m pieces D B (fun j => (hK j).isClosed) hD
  have hEq := incident_envelope_eq_metricJacobian_ae metricY I R J U f hU hf P A T m pieces D B (hLifts T) hT hBound
  have hGraph : Measurable (fun x => (x,R.polar T.val x)) := measurable_id.prodMk (R.polar_measurable T.val)
  have hBase : (∫ p, env p ∂(orientedTangentMeasure R T.val : Measure (EuclideanAmbient d × EuclideanExterior d k))) =
      J.mass (P.push k T) := by
    change (∫ p, env p ∂Measure.map (fun x => (x,R.polar T.val x)) (R.massMeasure T.val : Measure (EuclideanAmbient d))) = _
    rw [integral_map hGraph.aemeasurable hEnv.measurable.aestronglyMeasurable]
    exact (integral_congr_ae hEq).trans (A.mass_area_eq_of_injective k T hInjective).symm
  obtain ⟨M,hM⟩ := exteriorIncidentEnvelope_bounded (k := k) m pieces D B
  intro ε hε
  have hPortBound := hPort _ (fun i => orientedTangentMeasure R (Qi i).val) (orientedTangentMeasure R T.val)
    hWeak env M hEnv hM ε hε
  rw [hBase] at hPortBound
  filter_upwards [hPortBound] with i hi
  exact (push_mass_le_incident_envelope metricY I R J U f hU hf P A (Qi i) m pieces D
    (fun j => (hK j).isClosed) hD (hLifts (Qi i)) (hQi i) B hBound).trans hi

theorem sharp_pushed_mass_tendsto (hPort : UpperPortmanteauInput.{0})
    (T : supportedCurrents I U k) (Qi : ℕ → supportedCurrents I U k) (Si : ℕ → supportedCurrents I U (k+1))
    (hHom : ∀ i, T.val-(Qi i).val = I.boundary k (Si i).val)
    (hFill : Tendsto (fun i => I.mass (Si i).val) atTop (𝓝 0))
    (N : Set (EuclideanAmbient d)) (L : NNReal)
    (hLip : letI := metricY; LipschitzOnWith L f N) (hSupport : ∀ i, I.support (Si i).val ⊆ N)
    {Idx : Type*} [Fintype Idx] (m : Idx → ℕ) (pieces : Idx → Set (EuclideanAmbient d))
    (D : ∀ j, EuclideanAmbient d → Matrix (Fin (m j)) (Fin d) ℝ)
    (hK : ∀ j, IsCompact (pieces j)) (hD : ∀ j, ContinuousOn (D j) (pieces j))
    (hLifts : ∀ C : supportedCurrents I U k, ∀ j,
      ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), x ∈ pieces j →
        A.metricJacobian k C x = exteriorJacobian (k := k) (D j x) (R.polar C.val x))
    (hT : I.support T.val ⊆ ⋃ j, pieces j) (hQi : ∀ i, I.support (Qi i).val ⊆ ⋃ j, pieces j)
    (hInjective : Set.InjOn f (I.support T.val))
    (hWeak : Tendsto (fun i => orientedTangentMeasure R (Qi i).val) atTop (𝓝 (orientedTangentMeasure R T.val))) :
    Tendsto (fun i => J.mass (P.push k (Qi i))) atTop (𝓝 (J.mass (P.push k T))) := by
  apply pushed_mass_tendsto_of_sharp_upper P k T Qi Si hHom
  · exact pushed_fillings_mass_tendsto_zero P k Si N L hLip hSupport hFill
  · exact sharp_push_mass_upper metricY I R J U f hU hf P A hPort T Qi m pieces D hK hD hLifts hT hQi hInjective hWeak

end Paper28
