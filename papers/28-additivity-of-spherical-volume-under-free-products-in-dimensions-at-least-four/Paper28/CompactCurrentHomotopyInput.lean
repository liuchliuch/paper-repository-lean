import Paper28.RelativeCarrierDeformation
import Paper28.NeighborhoodPushforwardInput

/-! Standard AK local mass/locality and interval-product calculus, on
actual supported current groups and actual Lipschitz homotopies. All maps
and homotopies are arbitrary. No finite carrier, deformation, near-isometry,
sharp approximation, polyhedral filling or transfer is supplied. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
universe u v
variable {X : Type u} {metricX : MetricSpace X}
  (I : CompactIntegralCurrentAlgebraInput.{u,v} X metricX)

def supportedCurrentWeaken (K U : Set X) (hKU : K ⊆ U) (k : ℕ) :
    supportedCurrents I K k →+ supportedCurrents I U k where
  toFun C := ⟨C.val,C.property.trans hKU⟩
  map_zero' := rfl
  map_add' _ _ := rfl

structure LocalCurrentPushforwardCalculusInput
    (U : Set X) (f : X → X)
    (hU : @IsOpen X metricX.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U)
    (hf : LipschitzNearSet metricX metricX f U)
    (P : NeighborhoodCurrentPushforwardInput metricX metricX I I U f hU hf) : Prop where
  identity_on_support : ∀ k (C : supportedCurrents I U k),
    (∀ x ∈ I.support C.val, f x = x) → P.push k C = C.val
  mass_local_lipschitz_le : ∀ k (C : supportedCurrents I U k) (L : NNReal),
    (letI := metricX; ∀ x ∈ I.support C.val, ∃ V : Set X,
      V ∈ 𝓝 x ∧ LipschitzOnWith L f V) → I.mass (P.push k C) ≤ (L : ℝ)^k*I.mass C.val

structure CompactCurrentHomotopyInput where
  homotopyPush : ∀ (K : Set X) (H : DeformationInterval×K → X)
    (hH : letI := metricX; ∃ B : NNReal, LipschitzWith B H) (k : ℕ),
    supportedCurrents I K k →+ I.Current (k+1)
  boundary_formula : ∀ (U : Set X) (f : X → X)
    (hU : @IsOpen X metricX.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace U)
    (hf : LipschitzNearSet metricX metricX f U)
    (P : NeighborhoodCurrentPushforwardInput metricX metricX I I U f hU hf)
    (K : Set X) (hKU : K ⊆ U) (H : DeformationInterval×K → X)
    (hH : letI := metricX; ∃ B : NNReal, LipschitzWith B H)
    (_h0 : ∀ x : K, H (⟨0,by norm_num⟩,x) = x.val)
    (_h1 : ∀ x : K, H (⟨1,by norm_num⟩,x) = f x.val)
    (k : ℕ) (C : supportedCurrents I K (k+1)),
    I.boundary (k+1) (homotopyPush K H hH (k+1) C) =
      P.push (k+1) (supportedCurrentWeaken I K U hKU (k+1) C)-C.val-
        homotopyPush K H hH k (supportedBoundary I K k C)

end Paper28
