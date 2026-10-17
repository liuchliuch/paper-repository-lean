import Paper28.IndexedBarycentricCells
import Paper28.LiftableSphericalSimplex

/-! Every actual ordered signed barycentric face-chain simplex is a
source LiftableSphericalSimplex: its unit independent finite-support
vertices, common hemisphere, closed quotient injectivity and local round
isometry along the relative interior are all constructed natively. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G] [Countable G] {k : ℕ}

def signedBarycentricLiftableSimplex (M : SphericalQuotientMetricInput G) (A : Finset G)
    (σ : Fin (k+1) → Finset G) (hσ : Function.Injective σ) (hFaces : ∀ i, (σ i).Nonempty)
    (hChain : ∀ i j, σ i ⊆ σ j ∨ σ j ⊆ σ i) : LiftableSphericalSimplex M k where
  vertices i := ⟨signedFaceCenter A (σ i),signedFaceCenter_unit A (σ i) (hFaces i)⟩
  independent := indexedChain_centers_linearIndependent A σ hσ hFaces hChain
  coordinates := Finset.univ.biUnion σ
  supported i := signedFaceCenter_mem_coordinates A (σ i) _ (Finset.subset_biUnion_of_mem σ (Finset.mem_univ i))
  center := signedFaceVector A (Finset.univ.biUnion σ)
  hemisphere i := signedFaceCenter_hemisphere A _ (σ i)
    (Finset.subset_biUnion_of_mem σ (Finset.mem_univ i)) (hFaces i)
  quotient_injective := (signed_barycentric_cell_quotient_injective A (indexedChainFaces σ)
    (indexedChain_chain σ hChain)).mono (indexedChain_closed_cell A σ hσ)
  quotient_locally_isometric := by
    intro t ht u hu
    obtain ⟨r,hr,hRound⟩ := signed_barycentric_cell_quotient_locally_round M A (indexedChainFaces σ)
      (indexedChain_chain σ hChain) (indexedChain_faces_nonempty σ hFaces) u
      (indexedChain_strict_cell A σ hσ t ht u hu)
    refine ⟨r,hr,?_⟩
    intro v w hv hw hvu hwu
    exact hRound v (indexedChain_closed_cell A σ hσ hv) w (indexedChain_closed_cell A σ hσ hw) hvu hwu

theorem liftable_simplex_patch_subset_carrier (M : SphericalQuotientMetricInput G)
    (τ : LiftableSphericalSimplex M k) (families : Finset (Finset G))
    (γ : G) (E : Finset G) (hE : E ∈ families) (hCoordinates : τ.coordinates ⊆ E.image (fun g => γ*g)) :
    τ.projectedPatch ⊆ quotientFiniteCarrier families := by
  rintro q ⟨u,hu,rfl⟩
  refine ⟨u,⟨γ,E,hE,u.property,?_⟩,rfl⟩
  apply coordinateSupportSubspace_mono τ.coordinates _ hCoordinates
  exact sphericalSimplexPatch_mem_subspace (fun i => (τ.vertices i).val)
    (coordinateSupportSubspace τ.coordinates) τ.supported hu

end Paper28
