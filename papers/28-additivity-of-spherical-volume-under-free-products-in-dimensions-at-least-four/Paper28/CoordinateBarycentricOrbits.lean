import Paper28.CoordinateCrossPolytopeFaces
import Paper28.RelativeEquivariance
import Mathlib.Data.Finset.Max

/-! Actual normalized face barycenters, no inversions of their finite face
chains, and explicit finite orbit representatives for all barycentric cells
of the lifted finite-coordinate carrier. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def coordinateFaceBarycenter (F : Finset (SignedCoordinate G)) : CoordinateHilbert G :=
  sphericalNormalize (∑ v ∈ F, signedCoordinateVector v)

theorem coordinateFaceBarycenter_equivariant (γ : G) (F : Finset (SignedCoordinate G)) :
    leftRegular γ (coordinateFaceBarycenter F) = coordinateFaceBarycenter (coordinateFaceTranslate γ F) := by
  have hs : (∑ v ∈ coordinateFaceTranslate γ F, signedCoordinateVector v) =
      leftRegular γ (∑ v ∈ F, signedCoordinateVector v) := by
    rw [coordinateFaceTranslate,Finset.sum_map,map_sum]
    apply Finset.sum_congr rfl
    intro v _
    exact (signedCoordinateVector_equivariant γ v).symm
  rw [coordinateFaceBarycenter,coordinateFaceBarycenter,hs,sphericalNormalize_map]

def CoordinateBarycentricCell (families : Finset (Finset G)) (C : Finset (Finset (SignedCoordinate G))) : Prop :=
  C.Nonempty ∧ (∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) ∧ ∀ F ∈ C, CoordinateCrossFace families F

theorem finite_face_chain_has_maximum {α : Type*} [DecidableEq α] (C : Finset (Finset α))
    (hC : C.Nonempty) (hChain : ∀ F ∈ C, ∀ E ∈ C, F ⊆ E ∨ E ⊆ F) :
    ∃ E ∈ C, ∀ F ∈ C, F ⊆ E := by
  obtain ⟨E,hE,hMax⟩ := Finset.exists_max_image C Finset.card hC
  refine ⟨E,hE,?_⟩
  intro F hF
  rcases hChain F hF E hE with h | h
  · exact h
  · have he : F = E := (Finset.eq_of_subset_of_card_le h (hMax F hF)).symm
    rw [he]

def coordinateBarycentricSeeds (families : Finset (Finset G)) : Finset (Finset (Finset (SignedCoordinate G))) :=
  families.biUnion (fun E => (E ×ˢ (Finset.univ : Finset Bool)).powerset.powerset)

theorem coordinate_barycentric_cell_finite_orbit_representatives
    (families : Finset (Finset G)) (C : Finset (Finset (SignedCoordinate G)))
    (hC : CoordinateBarycentricCell families C) :
    ∃ γ : G, C.image (coordinateFaceTranslate γ) ∈ coordinateBarycentricSeeds families := by
  obtain ⟨F,hF,hMax⟩ := finite_face_chain_has_maximum C hC.1 hC.2.1
  obtain ⟨γ,E,hE,hFE⟩ := (hC.2.2 F hF).2.2
  refine ⟨γ⁻¹,Finset.mem_biUnion.mpr ⟨E,hE,Finset.mem_powerset.mpr ?_⟩⟩
  intro A hA
  obtain ⟨B,hB,he⟩ := Finset.mem_image.mp hA
  rw [← he]
  apply Finset.mem_powerset.mpr
  exact coordinateFaceTranslate_inv_subset ((Finset.image_subset_image (hMax B hB)).trans hFE)

theorem coordinate_barycentric_cell_stabilizer_fixes_vertices
    (families : Finset (Finset G)) (C : Finset (Finset (SignedCoordinate G)))
    (hC : CoordinateBarycentricCell families C) (γ : G)
    (hPres : C.image (coordinateFaceTranslate γ) = C) :
    ∀ F ∈ C, leftRegular γ (coordinateFaceBarycenter F) = coordinateFaceBarycenter F := by
  intro F hF
  have he : coordinateFaceTranslate γ F = F :=
    faceChain_preserving_equiv_fixes_faces C hC.2.1 (signedCoordinateEquiv γ) hPres F hF
  rw [coordinateFaceBarycenter_equivariant,he]

end Paper28
