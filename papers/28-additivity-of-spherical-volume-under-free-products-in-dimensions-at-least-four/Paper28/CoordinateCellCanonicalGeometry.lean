import Paper28.CanonicalSignedFaceModel
import Paper28.CoordinateCarrierBarycentricCells
import Paper28.SignedBarycentricRoundCharts

/-! Every actual carrier barycentric orbit representative has the proved
signed-coordinate geometric model. Closed quotient injectivity and local
roundness transfer to its actual full coordinate-face formulas. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

theorem coordinateChainProjection_chain (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) :
    ∀ F ∈ coordinateChainProjection C, ∀ E ∈ coordinateChainProjection C, F ⊆ E ∨ E ⊆ F := by
  intro F hF E hE
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hF
  obtain ⟨Q,hQ,rfl⟩ := Finset.mem_image.mp hE
  exact (hC.2.1 P hP Q hQ).imp Finset.image_subset_image Finset.image_subset_image

theorem coordinateChainProjection_nonempty_faces (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) :
    ∀ F ∈ coordinateChainProjection C, F.Nonempty := by
  intro F hF
  obtain ⟨P,hP,rfl⟩ := Finset.mem_image.mp hF
  exact (hC.2.2 P hP).1.image _

theorem coordinate_cell_to_signed_cell (A : Finset G) (D : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hModel : signedCoordinateFaceChain A D = C) :
    closedCoordinateBarycentricCell C ⊆ closedSignedBarycentricCell A D := by
  rintro u ⟨w,hw,hu⟩
  let z : Finset G → ℝ := fun F => w (signedCoordinateFace A F)
  refine ⟨z,?_,?_⟩
  · intro F hF
    apply hw
    rw [← hModel]
    exact Finset.mem_image.mpr ⟨F,hF,rfl⟩
  · have hs : (∑ F ∈ C, w F • coordinateFaceBarycenter F) = signedChainRaw A D z := by
      rw [← hModel]
      unfold signedCoordinateFaceChain signedChainRaw
      rw [Finset.sum_image (fun F _ E _ he => signedCoordinateFace_injective A he)]
      apply Finset.sum_congr rfl
      intro F _
      rw [coordinateFaceBarycenter_signed]
    rw [signedChainPoint,← hs]
    exact hu

def strictCoordinateBarycentricCell (C : Finset (Finset (SignedCoordinate G))) : Set (RegularSphere G) :=
  {u | ∃ w : Finset (SignedCoordinate G) → ℝ, (∀ F ∈ C, 0 < w F) ∧
    u.val = sphericalNormalize (∑ F ∈ C, w F • coordinateFaceBarycenter F)}

theorem coordinate_strict_cell_to_signed_cell (A : Finset G) (D : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hModel : signedCoordinateFaceChain A D = C) :
    strictCoordinateBarycentricCell C ⊆ strictSignedBarycentricCell A D := by
  rintro u ⟨w,hw,hu⟩
  let z : Finset G → ℝ := fun F => w (signedCoordinateFace A F)
  refine ⟨z,?_,?_⟩
  · intro F hF
    apply hw
    rw [← hModel]
    exact Finset.mem_image.mpr ⟨F,hF,rfl⟩
  · have hs : (∑ F ∈ C, w F • coordinateFaceBarycenter F) = signedChainRaw A D z := by
      rw [← hModel]
      unfold signedCoordinateFaceChain signedChainRaw
      rw [Finset.sum_image (fun F _ E _ he => signedCoordinateFace_injective A he)]
      apply Finset.sum_congr rfl
      intro F _
      rw [coordinateFaceBarycenter_signed]
    rw [signedChainPoint,← hs]
    exact hu

theorem coordinate_barycentric_cell_quotient_injective (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) :
    Set.InjOn (regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) (closedCoordinateBarycentricCell C) := by
  obtain ⟨A,hA⟩ := coordinate_cell_has_canonical_signed_model families C hC
  exact (signed_barycentric_cell_quotient_injective A (coordinateChainProjection C)
    (coordinateChainProjection_chain families C hC)).mono (coordinate_cell_to_signed_cell A _ C hA)

theorem coordinate_barycentric_cell_quotient_locally_round [Countable G]
    (M : SphericalQuotientMetricInput G) (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C)
    (u : RegularSphere G) (hu : u ∈ strictCoordinateBarycentricCell C) :
    ∃ r : ℝ, 0 < r ∧ ∀ v ∈ closedCoordinateBarycentricCell C, ∀ w ∈ closedCoordinateBarycentricCell C,
      dist v u < r → dist w u < r →
      @dist (RegularOrbitQuotient G) M.metric.toDist (regularQuotientMap v) (regularQuotientMap w) = angular v.val w.val := by
  obtain ⟨A,hA⟩ := coordinate_cell_has_canonical_signed_model families C hC
  obtain ⟨r,hr,hRound⟩ := signed_barycentric_cell_quotient_locally_round M A (coordinateChainProjection C)
    (coordinateChainProjection_chain families C hC) (coordinateChainProjection_nonempty_faces families C hC) u
    (coordinate_strict_cell_to_signed_cell A _ C hA hu)
  exact ⟨r,hr,fun v hv w hw => hRound v (coordinate_cell_to_signed_cell A _ C hA hv)
    w (coordinate_cell_to_signed_cell A _ C hA hw)⟩

end Paper28
