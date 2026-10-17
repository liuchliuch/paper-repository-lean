import Paper28.SignedCoordinateFaceModel

/-! The entire actual lifted finite-coordinate carrier is covered by its
actual signed barycentric cells. This is a native geometric cover tied to
the same finite face-chain orbit model used for the quotient. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def closedCoordinateBarycentricCell (C : Finset (Finset (SignedCoordinate G))) : Set (RegularSphere G) :=
  {u | ∃ w : Finset (SignedCoordinate G) → ℝ, (∀ F ∈ C, 0 ≤ w F) ∧
    u.val = sphericalNormalize (∑ F ∈ C, w F • coordinateFaceBarycenter F)}

theorem signed_cell_in_coordinate_face_chain (A : Finset G) (C : Finset (Finset G)) :
    closedSignedBarycentricCell A C ⊆ closedCoordinateBarycentricCell (signedCoordinateFaceChain A C) := by
  rintro u ⟨w,hw,hu⟩
  let W : Finset (SignedCoordinate G) → ℝ := fun F => w (F.image Prod.fst)
  refine ⟨W,?_,?_⟩
  · intro F hF
    obtain ⟨E,hE,he⟩ := Finset.mem_image.mp hF
    rw [← he]
    change 0 ≤ w ((signedCoordinateFace A E).image Prod.fst)
    rw [signedCoordinateFace_fst]
    exact hw E hE
  · have hs : (∑ F ∈ signedCoordinateFaceChain A C, W F • coordinateFaceBarycenter F) = signedChainRaw A C w := by
      unfold signedCoordinateFaceChain signedChainRaw
      rw [Finset.sum_image (fun F _ E _ he => signedCoordinateFace_injective A he)]
      apply Finset.sum_congr rfl
      intro F _
      change w ((signedCoordinateFace A F).image Prod.fst) • coordinateFaceBarycenter (signedCoordinateFace A F) = _
      rw [signedCoordinateFace_fst,coordinateFaceBarycenter_signed]
    rw [hs]
    exact hu

theorem lifted_coordinate_carrier_barycentric_cover (families : Finset (Finset G))
    (u : RegularSphere G) (hu : u.val ∈ liftedFiniteCarrier families) :
    ∃ C : Finset (Finset (SignedCoordinate G)), CoordinateBarycentricCell families C ∧
      u ∈ closedCoordinateBarycentricCell C := by
  obtain ⟨γ,E,hE,_,hSupport⟩ := hu
  obtain ⟨A,hAF,C,hC,hFaces,hChain,huC⟩ := coordinate_sphere_barycentric_cover
    (E.image (fun g => γ*g)) u hSupport
  refine ⟨signedCoordinateFaceChain A C,
    signedCoordinateFaceChain_cell A _ C families hC hFaces hChain γ E hE (Subset.refl _),?_⟩
  apply signed_cell_in_coordinate_face_chain A C
  obtain ⟨w,hw,he⟩ := huC
  exact ⟨w,fun F hF => (hw F hF).le,he⟩

end Paper28
