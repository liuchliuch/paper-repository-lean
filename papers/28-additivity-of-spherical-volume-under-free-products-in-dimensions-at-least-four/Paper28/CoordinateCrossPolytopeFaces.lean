import Paper28.BarycentricFaceRanks
import Paper28.L2Reindex
import Paper28.CoordinateCarriers

/-! Actual signed coordinate vertices and finite-coordinate cross-polytope
faces. The explicit finite orbit representatives are constructed from the
coordinate families, without assuming a quotient triangulation exists. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

abbrev SignedCoordinate (G : Type*) := G×Bool

def signedCoordinateEquiv (γ : G) : SignedCoordinate G ≃ SignedCoordinate G :=
  (Equiv.mulLeft γ).prodCongr (Equiv.refl Bool)

def coordinateFaceTranslate (γ : G) (F : Finset (SignedCoordinate G)) : Finset (SignedCoordinate G) :=
  F.map (signedCoordinateEquiv γ).toEmbedding

def signedCoordinateVector (s : SignedCoordinate G) : CoordinateHilbert G :=
  lp.single 2 s.1 (if s.2 then 1 else -1)

theorem signedCoordinateVector_equivariant (γ : G) (s : SignedCoordinate G) :
    leftRegular γ (signedCoordinateVector s) = signedCoordinateVector (signedCoordinateEquiv γ s) := by
  ext g
  by_cases h : γ*s.1 = g
  · subst g
    simp [signedCoordinateVector,signedCoordinateEquiv]
  · have hi : γ⁻¹*g ≠ s.1 := by
      intro he
      apply h
      rw [← he,mul_inv_cancel_left]
    simp [signedCoordinateVector,signedCoordinateEquiv,h,hi,Ne.symm h]

def CoordinateCrossFace (families : Finset (Finset G)) (F : Finset (SignedCoordinate G)) : Prop :=
  F.Nonempty ∧ (∀ g, ¬((g,true) ∈ F ∧ (g,false) ∈ F)) ∧
    ∃ γ : G, ∃ E ∈ families, F.image Prod.fst ⊆ E.image (fun g => γ*g)

def coordinateFaceSeeds (families : Finset (Finset G)) : Finset (Finset (SignedCoordinate G)) :=
  families.biUnion (fun E => (E ×ˢ (Finset.univ : Finset Bool)).powerset)

theorem coordinateFaceTranslate_inv_subset {γ : G} {E : Finset G} {F : Finset (SignedCoordinate G)}
    (hF : F.image Prod.fst ⊆ E.image (fun g => γ*g)) :
    coordinateFaceTranslate γ⁻¹ F ⊆ E ×ˢ (Finset.univ : Finset Bool) := by
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨g,hg,he⟩ := Finset.mem_image.mp (hF (Finset.mem_image.mpr ⟨w,hw,rfl⟩))
  apply Finset.mem_product.mpr
  refine ⟨?_,Finset.mem_univ _⟩
  change γ⁻¹*w.1 ∈ E
  rw [← he,inv_mul_cancel_left]
  exact hg

theorem coordinate_cross_face_finite_orbit_representatives
    (families : Finset (Finset G)) (F : Finset (SignedCoordinate G)) (hF : CoordinateCrossFace families F) :
    ∃ γ : G, coordinateFaceTranslate γ F ∈ coordinateFaceSeeds families := by
  obtain ⟨γ,E,hE,hFE⟩ := hF.2.2
  refine ⟨γ⁻¹,Finset.mem_biUnion.mpr ⟨E,hE,?_⟩⟩
  exact Finset.mem_powerset.mpr (coordinateFaceTranslate_inv_subset hFE)

end Paper28
