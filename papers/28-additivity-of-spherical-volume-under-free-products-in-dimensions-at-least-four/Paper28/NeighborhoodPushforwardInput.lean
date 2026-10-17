import Paper28.SupportedCurrents
import Paper28.CompactLocalLipschitz

/-! Generic AK pushforward on the actual supported-current subgroup of an
open neighborhood. The mass law is the standard individual Lipschitz area
estimate, not a sharp retraction or joint-transfer premise. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
universe u w v

def LipschitzNearSet {X : Type u} {Y : Type w} (metricX : MetricSpace X) (metricY : MetricSpace Y)
    (f : X → Y) (U : Set X) : Prop :=
  letI := metricX
  letI := metricY
  ∀ x ∈ U, ∃ L : NNReal, ∃ V : Set X, V ∈ 𝓝 x ∧ LipschitzOnWith L f V

theorem LipschitzNearSet.compact_restrict {X : Type u} {Y : Type w}
    [MetricSpace X] [MetricSpace Y] (f : X → Y) (U K : Set X)
    (hf : LipschitzNearSet inferInstance inferInstance f U) (hKU : K ⊆ U) (hK : IsCompact K) :
    ∃ L : NNReal, LipschitzWith L (fun x : K => f x.val) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  apply exists_lipschitzWith_of_compactSpace
  intro x
  obtain ⟨L,V,hV,hLip⟩ := hf x.val (hKU x.property)
  refine ⟨L,Subtype.val ⁻¹' V,continuous_subtype_val.continuousAt.preimage_mem_nhds hV,?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro y hy z hz
  exact hLip.dist_le_mul y.val hy z.val hz

structure NeighborhoodCurrentPushforwardInput
    {X : Type u} {Y : Type w} (metricX : MetricSpace X) (metricY : MetricSpace Y)
    (I : CompactIntegralCurrentAlgebraInput.{u,v} X metricX)
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set X) (f : X → Y)
    (hU : @IsOpen X metricX.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U)
    (hf : LipschitzNearSet metricX metricY f U) where
  push : ∀ k, supportedCurrents I U k →+ J.Current k
  boundary_comm : ∀ k (C : supportedCurrents I U (k+1)),
    J.boundary k (push (k+1) C) = push k (supportedBoundary I U k C)
  support_subset : ∀ k (C : supportedCurrents I U k),
    J.support (push k C) ⊆ f '' I.support C.val
  mass_lipschitz_le : ∀ k (C : supportedCurrents I U k) (L : NNReal),
    (letI := metricX; letI := metricY; LipschitzOnWith L f (I.support C.val)) →
      J.mass (push k C) ≤ (L : ℝ)^k*I.mass C.val

end Paper28
