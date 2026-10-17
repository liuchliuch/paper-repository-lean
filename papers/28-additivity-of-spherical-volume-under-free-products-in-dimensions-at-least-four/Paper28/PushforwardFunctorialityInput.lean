import Paper28.NeighborhoodPushforwardInput

/-! The standard composition/identity/locality law of canonical AK
pushforwards, specialized only to two composable neighborhood maps whose
composition is the identity on the current support. No spherical geometry,
deformation, approximation, mass estimate or filling is in this input. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe u w v

structure TwoStagePushforwardFunctorialityInput
    {X : Type u} {Y : Type w} (metricX : MetricSpace X) (metricY : MetricSpace Y)
    (I : CompactIntegralCurrentAlgebraInput.{u,v} X metricX)
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set X) (V : Set Y) (f : X → Y) (g : Y → X)
    (hU : @IsOpen X metricX.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U)
    (hV : @IsOpen Y metricY.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace V)
    (hf : LipschitzNearSet metricX metricY f U) (hg : LipschitzNearSet metricY metricX g V)
    (P : NeighborhoodCurrentPushforwardInput metricX metricY I J U f hU hf)
    (Q : NeighborhoodCurrentPushforwardInput metricY metricX J I V g hV hg) : Prop where
  composition_identity_on_support : ∀ k (C : supportedCurrents I U k)
    (hSupport : J.support (P.push k C) ⊆ V),
    (∀ x ∈ I.support C.val, g (f x) = x) → Q.push k ⟨P.push k C,hSupport⟩ = C.val

theorem lipschitzNearSet_of_lipschitzWith {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    (f : X → Y) (L : NNReal) (hf : LipschitzWith L f) (U : Set X) :
    LipschitzNearSet inferInstance inferInstance f U :=
  fun _ _ => ⟨L,Set.univ,Filter.univ_mem,hf.lipschitzOnWith⟩

end Paper28
