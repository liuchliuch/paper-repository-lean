import Paper28.CoordinateCellCanonicalGeometry
import Paper28.BarycentricLiftableSimplices
import Paper28.SphericalPositiveCone

/-! Every actual carrier cell is exactly an actual source liftable
geodesic simplex. Arbitrary nonnegative cone weights are normalized into
the actual standard simplex; all source geometric fields were proved. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G] {k : ℕ}

theorem closedSignedBarycentricCell_eq_indexed_patch (A : Finset G) (C : Finset (Finset G))
    (σ : Fin (k+1) → Finset G) (hσ : Function.Injective σ) (hC : Finset.univ.image σ = C) :
    closedSignedBarycentricCell A C =
      {u : RegularSphere G | u.val ∈ sphericalSimplexPatch (fun i => signedFaceCenter A (σ i))} := by
  apply Set.Subset.antisymm
  · rintro u ⟨w,hw,hu⟩
    have hRaw : signedChainRaw A C w = ∑ i, w (σ i) • signedFaceCenter A (σ i) := by
      unfold signedChainRaw
      rw [← hC,Finset.sum_image (fun i _ j _ he => hσ he)]
    have hMem : ∀ i, σ i ∈ C := by
      intro i
      rw [← hC]
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hUnit : ‖sphericalNormalize (∑ i, w (σ i) • signedFaceCenter A (σ i))‖ = 1 := by
      rw [← hRaw]
      change ‖signedChainPoint A C w‖ = 1
      exact hu ▸ u.property
    change u.val ∈ sphericalSimplexPatch (fun i => signedFaceCenter A (σ i))
    rw [hu,signedChainPoint,hRaw]
    exact normalized_nonnegative_sum_mem_sphericalSimplexPatch _ _ (fun i => hw _ (hMem i)) hUnit
  · intro u hu
    have he := indexedChain_closed_cell A σ hσ hu
    simpa only [indexedChainFaces,hC] using he

theorem coordinate_barycentric_cell_liftable_realization [Countable G]
    (M : SphericalQuotientMetricInput G) (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) :
    ∃ k : ℕ, ∃ τ : LiftableSphericalSimplex M k,
      {u : RegularSphere G | u.val ∈ sphericalSimplexPatch (fun i => (τ.vertices i).val)} =
        closedCoordinateBarycentricCell C := by
  obtain ⟨A,hModel⟩ := coordinate_cell_has_canonical_signed_model families C hC
  let D := coordinateChainProjection C
  have hD : D.Nonempty := hC.1.image _
  obtain ⟨k,σ,hσ,hEnum⟩ := nonempty_finset_indexing D hD
  have hMem : ∀ i, σ i ∈ D := by
    intro i
    rw [← hEnum]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hFaces : ∀ i, (σ i).Nonempty := fun i => coordinateChainProjection_nonempty_faces families C hC _ (hMem i)
  have hChain : ∀ i j, σ i ⊆ σ j ∨ σ j ⊆ σ i := fun i j => coordinateChainProjection_chain families C hC
    _ (hMem i) _ (hMem j)
  let τ := signedBarycentricLiftableSimplex M A σ hσ hFaces hChain
  refine ⟨k,τ,?_⟩
  change {u : RegularSphere G | u.val ∈ sphericalSimplexPatch (fun i => signedFaceCenter A (σ i))} = _
  have hGeom : closedCoordinateBarycentricCell C = closedSignedBarycentricCell A D := by
    apply Set.Subset.antisymm (coordinate_cell_to_signed_cell A D C hModel)
    intro u hu
    rw [← hModel]
    exact signed_cell_in_coordinate_face_chain A D hu
  exact (closedSignedBarycentricCell_eq_indexed_patch A D σ hσ hEnum).symm.trans hGeom.symm

theorem coordinate_barycentric_cell_projected_liftable_realization [Countable G]
    (M : SphericalQuotientMetricInput G) (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) :
    ∃ k : ℕ, ∃ τ : LiftableSphericalSimplex M k,
      τ.projectedPatch = regularQuotientMap '' closedCoordinateBarycentricCell C := by
  obtain ⟨k,τ,hτ⟩ := coordinate_barycentric_cell_liftable_realization M families C hC
  exact ⟨k,τ,congrArg (fun E : Set (RegularSphere G) => regularQuotientMap '' E) hτ⟩

end Paper28
