import Paper28.CoordinateBarycentricCellAction
import Paper28.CoordinateCarrierCompact

/-! The actual coordinate carrier is exactly the union of finitely many
actual quotient barycentric cells. The representative set, regular action,
coordinate supports and normalized cell formulas are all native. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type*} [Group G] [DecidableEq G]

def coordinateCarrierCellRepresentatives (families : Finset (Finset G)) :
    Finset (Finset (Finset (SignedCoordinate G))) :=
  (coordinateBarycentricSeeds families).filter (CoordinateBarycentricCell families)

theorem quotient_carrier_finite_barycentric_cover (families : Finset (Finset G))
    (q : RegularOrbitQuotient G) (hq : q ∈ quotientFiniteCarrier families) :
    ∃ C ∈ coordinateCarrierCellRepresentatives families,
      q ∈ regularQuotientMap '' closedCoordinateBarycentricCell C := by
  obtain ⟨u,hu,huq⟩ := hq
  obtain ⟨C,hC,huC⟩ := lifted_coordinate_carrier_barycentric_cover families u hu
  obtain ⟨γ,hSeed⟩ := coordinate_barycentric_cell_finite_orbit_representatives families C hC
  refine ⟨coordinateCellTranslate γ C,Finset.mem_filter.mpr ⟨hSeed,
    coordinateBarycentricCell_translate families C hC γ⟩,γ • u,
    closedCoordinateBarycentricCell_smul γ C u huC,?_⟩
  exact (regularQuotientMap_smul γ u).trans huq

theorem signedCoordinateVector_mem_coordinates (s : SignedCoordinate G) (E : Finset G) (hs : s.1 ∈ E) :
    signedCoordinateVector s ∈ coordinateSupportSubspace E := by
  intro g hg
  exact lp.single_apply_ne 2 s.1 _ (fun he => hg (he.symm ▸ hs))

theorem coordinateFaceBarycenter_mem_coordinates (F : Finset (SignedCoordinate G)) (E : Finset G)
    (hFE : F.image Prod.fst ⊆ E) : coordinateFaceBarycenter F ∈ coordinateSupportSubspace E := by
  apply (coordinateSupportSubspace E).smul_mem
  apply Submodule.sum_mem
  intro s hs
  exact signedCoordinateVector_mem_coordinates s E (hFE (Finset.mem_image.mpr ⟨s,hs,rfl⟩))

theorem coordinate_barycentric_cell_patch_subset_carrier (families : Finset (Finset G))
    (C : Finset (Finset (SignedCoordinate G))) (hC : CoordinateBarycentricCell families C) :
    regularQuotientMap '' closedCoordinateBarycentricCell C ⊆ quotientFiniteCarrier families := by
  obtain ⟨F,hF,hMax⟩ := finite_face_chain_has_maximum C hC.1 hC.2.1
  obtain ⟨γ,E,hE,hFE⟩ := (hC.2.2 F hF).2.2
  rintro q ⟨u,⟨w,_,hu⟩,rfl⟩
  refine ⟨u,⟨γ,E,hE,u.property,?_⟩,rfl⟩
  rw [hu]
  apply (coordinateSupportSubspace (E.image (fun g => γ*g))).smul_mem
  apply Submodule.sum_mem
  intro P hP
  apply Submodule.smul_mem
  exact coordinateFaceBarycenter_mem_coordinates P _ ((Finset.image_subset_image (hMax P hP)).trans hFE)

theorem quotientFiniteCarrier_eq_finite_barycentric_cells (families : Finset (Finset G)) :
    quotientFiniteCarrier families = ⋃ C ∈ coordinateCarrierCellRepresentatives families,
      regularQuotientMap '' closedCoordinateBarycentricCell C := by
  ext q
  constructor
  · intro hq
    obtain ⟨C,hC,hqC⟩ := quotient_carrier_finite_barycentric_cover families q hq
    exact mem_iUnion.mpr ⟨C,mem_iUnion.mpr ⟨hC,hqC⟩⟩
  · intro hq
    obtain ⟨C,hC⟩ := mem_iUnion.mp hq
    obtain ⟨hC,hqC⟩ := mem_iUnion.mp hC
    exact coordinate_barycentric_cell_patch_subset_carrier families C (Finset.mem_filter.mp hC).2 hqC

end Paper28
