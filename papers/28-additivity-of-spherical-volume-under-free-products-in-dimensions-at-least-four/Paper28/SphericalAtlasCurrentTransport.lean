import Paper28.AtlasSphericalMap
import Paper28.PushforwardFunctorialityInput
import Paper28.EuclideanPolyhedralCurrents

/-! Pull an actual current back by the actual inverse realization. Its
support is in the native carrier, cycles remain cycles, and the actual
constructed map pushes it back to precisely the original current. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe w v
variable {V Idx : Type*} [Fintype V] [DecidableEq V] [Fintype Idx]
  {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  (B : FullSubcomplexBarycentricAtlas K V Idx) {Y : Type w} [metricY : MetricSpace Y]

def atlasInverseMap (h : K.complex.space ≃ₜ Y) (y : Y) : EuclideanAmbient d := (h.symm y).val

theorem atlasInverseMap_lipschitz (h : K.complex.space ≃ₜ Y) (M : NNReal)
    (hh : LipschitzWith M h.symm) : LipschitzWith M (atlasInverseMap h) := by
  simpa only [one_mul] using isometry_subtype_coe.lipschitz.comp hh

theorem atlasInverseMap_near_lipschitz (h : K.complex.space ≃ₜ Y) (M : NNReal)
    (hh : LipschitzWith M h.symm) :
    LipschitzNearSet metricY inferInstance (atlasInverseMap h) Set.univ :=
  lipschitzNearSet_of_lipschitzWith _ M (atlasInverseMap_lipschitz h M hh) _

theorem atlasSphericalMap_inverseMap (h : K.complex.space ≃ₜ Y) (y₀ : Y) (y : Y) :
    atlasSphericalMap B h y₀ (atlasInverseMap h y) = y :=
  (atlasSphericalMap_on_carrier B h y₀ (h.symm y)).trans (h.apply_symm_apply y)

variable (h : K.complex.space ≃ₜ Y) (M : NNReal) (hh : LipschitzWith M h.symm)
  (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
  (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
  (Pull : NeighborhoodCurrentPushforwardInput metricY inferInstance J I Set.univ
    (atlasInverseMap h) isOpen_univ (atlasInverseMap_near_lipschitz h M hh))

def atlasPullbackValue {k : ℕ} (C : J.Current k) : I.Current k :=
  Pull.push k ⟨C,Set.subset_univ _⟩

theorem atlasPullback_support {k : ℕ} (C : J.Current k) :
    I.support (atlasPullbackValue h M hh I J Pull C) ⊆ K.complex.space := by
  intro x hx
  obtain ⟨y,_,rfl⟩ := Pull.support_subset k ⟨C,Set.subset_univ _⟩ hx
  exact (h.symm y).property

def atlasPullback {k : ℕ} (C : J.Current k) : supportedCurrents I (atlasRetractionDomain B) k :=
  ⟨atlasPullbackValue h M hh I J Pull C,
    (atlasPullback_support h M hh I J Pull C).trans (atlasRetractionDomain_contains B)⟩

theorem atlasPullback_cycle {k : ℕ} (C : J.Current (k+1)) (hC : J.boundary k C = 0) :
    I.boundary k (atlasPullback B h M hh I J Pull C).val = 0 := by
  change I.boundary k (Pull.push (k+1) ⟨C,Set.subset_univ _⟩) = 0
  rw [Pull.boundary_comm]
  have hz : supportedBoundary J Set.univ k ⟨C,Set.subset_univ _⟩ = 0 := Subtype.ext hC
  rw [hz,map_zero]

theorem atlasPullback_push_identity (y₀ : Y)
    (hf : LipschitzNearSet inferInstance metricY (atlasSphericalMap B h y₀) (atlasRetractionDomain B))
    (Push : NeighborhoodCurrentPushforwardInput inferInstance metricY I J (atlasRetractionDomain B)
      (atlasSphericalMap B h y₀) (atlasRetractionDomain_isOpen B) hf)
    (F : TwoStagePushforwardFunctorialityInput metricY inferInstance J I Set.univ
      (atlasRetractionDomain B) (atlasInverseMap h) (atlasSphericalMap B h y₀)
      isOpen_univ (atlasRetractionDomain_isOpen B) (atlasInverseMap_near_lipschitz h M hh) hf Pull Push)
    {k : ℕ} (C : J.Current k) : Push.push k (atlasPullback B h M hh I J Pull C) = C := by
  apply F.composition_identity_on_support k ⟨C,Set.subset_univ _⟩
    ((atlasPullback_support h M hh I J Pull C).trans (atlasRetractionDomain_contains B))
  intro y _
  exact atlasSphericalMap_inverseMap B h y₀ y

end Paper28
