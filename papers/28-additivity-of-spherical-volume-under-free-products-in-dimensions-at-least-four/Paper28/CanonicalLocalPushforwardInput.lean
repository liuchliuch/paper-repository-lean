import Paper28.CompactCurrentHomotopyInput

/-! Universal standard canonical AK local pushforward existence, with
only generic locality and individual local mass calculus. This factory
has no carrier, near-isometry, approximation or filling conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
universe u v
variable {X : Type u} {metric : MetricSpace X}

structure CanonicalLocalPushforwardInput
    (I : CompactIntegralCurrentAlgebraInput.{u,v} X metric) : Prop where
  pushforward : ∀ (U : Set X) (f : X → X)
    (hU : @IsOpen X metric.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U)
    (hf : LipschitzNearSet metric metric f U),
    ∃ P : NeighborhoodCurrentPushforwardInput metric metric I I U f hU hf,
      LocalCurrentPushforwardCalculusInput I U f hU hf P

end Paper28
