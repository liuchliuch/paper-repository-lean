import Paper28.BarycentricAtlasRegularity
import Paper28.NeighborhoodPushforwardInput

/-! The actual map h composed with the constructed neighborhood retraction.
Its relative identity, injectivity on the carrier and local Lipschitz
regularity are proved directly on the actual domain. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter Set
open scoped Topology
variable {H V Idx Y : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [DecidableEq H]
  [Fintype V] [DecidableEq V] [Fintype Idx] [MetricSpace Y]
variable {K : FiniteEuclideanComplex H} (A : FullSubcomplexBarycentricAtlas K V Idx)

def atlasSphericalMap (h : K.complex.space → Y) (y₀ : Y) (x : H) : Y := by
  classical
  exact if hx : x ∈ atlasRetractionDomain A then h ⟨atlasRetraction A x,atlasRetraction_mapsTo A hx⟩ else y₀

theorem atlasSphericalMap_on_domain (h : K.complex.space → Y) (y₀ : Y) (x : H)
    (hx : x ∈ atlasRetractionDomain A) :
    atlasSphericalMap A h y₀ x = h ⟨atlasRetraction A x,atlasRetraction_mapsTo A hx⟩ := by
  rw [atlasSphericalMap,dif_pos hx]

theorem atlasSphericalMap_on_carrier (h : K.complex.space → Y) (y₀ : Y) (x : K.complex.space) :
    atlasSphericalMap A h y₀ x.val = h x := by
  rw [atlasSphericalMap_on_domain A h y₀ x.val (atlasRetractionDomain_contains A x.property)]
  congr 1
  exact Subtype.ext (atlasRetraction_fixed A x.val x.property)

theorem atlasSphericalMap_injective_on_carrier (h : K.complex.space → Y) (y₀ : Y)
    (hh : Function.Injective h) : Set.InjOn (atlasSphericalMap A h y₀) K.complex.space := by
  intro x hx y hy he
  have he' : h (⟨x,hx⟩ : K.complex.space) = h (⟨y,hy⟩ : K.complex.space) := by
    exact (atlasSphericalMap_on_carrier A h y₀ ⟨x,hx⟩).symm.trans
      (he.trans (atlasSphericalMap_on_carrier A h y₀ ⟨y,hy⟩))
  exact congrArg Subtype.val (hh he')

theorem atlasSphericalMap_near_lipschitz (h : K.complex.space → Y) (y₀ : Y)
    (Lh : NNReal) (hh : LipschitzWith Lh h) :
    LipschitzNearSet inferInstance inferInstance (atlasSphericalMap A h y₀) (atlasRetractionDomain A) := by
  intro x hx
  obtain ⟨L,S,hS,hLip⟩ := atlasRetraction_near_lipschitz A x hx
  refine ⟨Lh*L,S ∩ atlasRetractionDomain A,
    inter_mem hS ((atlasRetractionDomain_isOpen A).mem_nhds hx),LipschitzOnWith.of_dist_le_mul ?_⟩
  intro y hy z hz
  rw [atlasSphericalMap_on_domain A h y₀ y hy.2,atlasSphericalMap_on_domain A h y₀ z hz.2]
  exact (hh.dist_le_mul _ _).trans (by
    simpa only [NNReal.coe_mul,mul_assoc] using mul_le_mul_of_nonneg_left
      (hLip.dist_le_mul y hy.1 z hz.1) Lh.coe_nonneg)

end Paper28
