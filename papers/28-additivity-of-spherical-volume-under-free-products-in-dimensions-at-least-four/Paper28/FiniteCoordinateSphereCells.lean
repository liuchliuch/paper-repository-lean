import Paper28.BarycentricCellSimplexRealization
import Paper28.CoordinateBarycentricCover
import Paper28.CoordinateCarrierCompact

/-! A finite coordinate sphere has an explicit finite closed cover by
compact actual barycentric cells. This prepares exact finite closed-cover
Lipschitz gluing for paths inside that coordinate sphere. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

theorem closedSignedBarycentricCell_isCompact (A : Finset G) (C : Finset (Finset G))
    (hC : C.Nonempty) (hFaces : ∀ F ∈ C, F.Nonempty) : IsCompact (closedSignedBarycentricCell A C) := by
  obtain ⟨k,σ,hσ,hEnum⟩ := nonempty_finset_indexing C hC
  have hMem : ∀ i, σ i ∈ C := by
    intro i
    rw [← hEnum]
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  let E := Finset.univ.biUnion σ
  have hHem : ∀ i, 0 < inner ℝ (signedFaceVector A E) (signedFaceCenter A (σ i)) := by
    intro i
    exact signedFaceCenter_hemisphere A E (σ i) (Finset.subset_biUnion_of_mem σ (Finset.mem_univ i)) (hFaces _ (hMem i))
  rw [closedSignedBarycentricCell_eq_indexed_patch A C σ hσ hEnum,Subtype.isCompact_iff]
  have he : Subtype.val '' {u : RegularSphere G | u.val ∈ sphericalSimplexPatch (fun i => signedFaceCenter A (σ i))} =
      sphericalSimplexPatch (fun i => signedFaceCenter A (σ i)) := by
    ext x
    constructor
    · rintro ⟨u,hu,rfl⟩
      exact hu
    · intro hx
      exact ⟨⟨x,sphericalSimplexPatch_unit _ (signedFaceVector A E) hHem x hx⟩,hx,rfl⟩
  rw [he]
  exact sphericalSimplexPatch_isCompact _ (signedFaceVector A E) hHem

def coordinateSphereCellIndices (E : Finset G) : Finset (Finset G × Finset (Finset G)) :=
  (E.powerset ×ˢ E.powerset.powerset).filter (fun p => p.2.Nonempty ∧
    (∀ F ∈ p.2, F.Nonempty) ∧ (∀ F ∈ p.2, ∀ D ∈ p.2, F ⊆ D ∨ D ⊆ F))

theorem coordinateSphereCellIndices_compact (E : Finset G) (p : Finset G × Finset (Finset G))
    (hp : p ∈ coordinateSphereCellIndices E) : IsCompact (closedSignedBarycentricCell p.1 p.2) := by
  obtain ⟨_,hc,hFaces,_⟩ := Finset.mem_filter.mp hp
  exact closedSignedBarycentricCell_isCompact p.1 p.2 hc hFaces

theorem coordinateSphere_finite_closed_cell_cover (E : Finset G) :
    regularCoordinateSphere E ⊆ ⋃ p ∈ coordinateSphereCellIndices E, closedSignedBarycentricCell p.1 p.2 := by
  intro u hu
  obtain ⟨A,hA,C,hC,hFaces,hChain,huC⟩ := coordinate_sphere_barycentric_cover E u hu
  apply mem_iUnion.mpr
  refine ⟨(A,C),mem_iUnion.mpr ⟨?_,?_⟩⟩
  · apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_powerset.mpr hA,Finset.mem_powerset.mpr ?_⟩,
      hC,fun F hF => (hFaces F hF).1,hChain⟩
    intro F hF
    exact Finset.mem_powerset.mpr (hFaces F hF).2
  · obtain ⟨w,hw,he⟩ := huC
    exact ⟨w,fun F hF => (hw F hF).le,he⟩

end Paper28
