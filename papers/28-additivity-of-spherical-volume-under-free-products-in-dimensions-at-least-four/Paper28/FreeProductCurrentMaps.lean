import Paper28.PaperFoundations
import Paper28.HomFoldPolyhedralPush

/-! Actual maps used in the additivity proof, packaged from the standard
objects. Polyhedral factor inclusions and the concrete transfer homomorphisms
are native definitions using the already proved generic/own constructions. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  {A B : Subgroup G}
  (DG : SphericalQuotientCurrentData Std.currentCalculus G)
  (DA : SphericalQuotientCurrentData Std.currentCalculus A)
  (DB : SphericalQuotientCurrentData Std.currentCalculus B)

def factorPolyhedralInclusionA (k : ℕ) :
    sphericalPolyhedralCurrents DA.simplex k →+ sphericalPolyhedralCurrents DG.simplex k :=
  homFoldPolyhedralPush DA.M DG.M DA.algebra DG.algebra DA.sphereAlgebra DG.sphereAlgebra
    DA.simplex DG.simplex DA.lifted DG.lifted Std.currentCalculus DA.gluing DG.gluing Std.injectiveFolding
    A.subtype Subtype.val_injective k

def factorPolyhedralInclusionB (k : ℕ) :
    sphericalPolyhedralCurrents DB.simplex k →+ sphericalPolyhedralCurrents DG.simplex k :=
  homFoldPolyhedralPush DB.M DG.M DB.algebra DG.algebra DB.sphereAlgebra DG.sphereAlgebra
    DB.simplex DG.simplex DB.lifted DG.lifted Std.currentCalculus DB.gluing DG.gluing Std.injectiveFolding
    B.subtype Subtype.val_injective k

def freeProductTransferA (T : BassSerreObject A B) (k : ℕ) :
    sphericalPolyhedralCurrents DG.simplex (k+1) →+ DA.algebra.Current (k+1) :=
  bassSerreTransferA DG.lifted Std.currentCalculus T DA.M DA.algebra DG.simplex DG.gluing DA.massFaithful k

def freeProductTransferB (T : BassSerreObject A B) (k : ℕ) :
    sphericalPolyhedralCurrents DG.simplex (k+1) →+ DB.algebra.Current (k+1) :=
  bassSerreTransferB DG.lifted Std.currentCalculus T DB.M DB.algebra DG.simplex DG.gluing DB.massFaithful k

theorem factorPolyhedralInclusionA_lifted (k : ℕ) (P : sphericalPolyhedralCurrents DA.simplex k) :
    ∃ z : FreeAbelianGroup (LiftableSphericalSimplex DA.M k),
    ∃ w : FreeAbelianGroup (LiftableSphericalSimplex DG.M k),
      projectedSphericalChain DA.simplex k z = P ∧
      projectedSphericalChain DG.simplex k w = factorPolyhedralInclusionA Std DG DA k P ∧
      liftedSphericalChain DG.lifted k w =
        finiteCoordinateSphereFoldPush DA.sphereAlgebra DG.sphereAlgebra Std.currentCalculus A.subtype k
          (liftedSphericalChain DA.lifted k z) := by
  obtain ⟨z,hz⟩ := projectedSphericalChain_surjective DA.simplex k P
  obtain ⟨w,hw⟩ := injective_geodesic_folding_chain DA.sphereAlgebra DG.sphereAlgebra Std.currentCalculus
    A.subtype Std.injectiveFolding DA.lifted DG.lifted Subtype.val_injective k z
  refine ⟨z,w,hz,?_,hw⟩
  apply Subtype.ext
  have he := homFold_projected_lift DA.M DG.M DA.algebra DG.algebra DA.sphereAlgebra DG.sphereAlgebra
    DA.simplex DG.simplex DA.lifted DG.lifted Std.currentCalculus DA.gluing DG.gluing A.subtype k z w hw
  rwa [hz] at he

theorem factorPolyhedralInclusionB_lifted (k : ℕ) (P : sphericalPolyhedralCurrents DB.simplex k) :
    ∃ z : FreeAbelianGroup (LiftableSphericalSimplex DB.M k),
    ∃ w : FreeAbelianGroup (LiftableSphericalSimplex DG.M k),
      projectedSphericalChain DB.simplex k z = P ∧
      projectedSphericalChain DG.simplex k w = factorPolyhedralInclusionB Std DG DB k P ∧
      liftedSphericalChain DG.lifted k w =
        finiteCoordinateSphereFoldPush DB.sphereAlgebra DG.sphereAlgebra Std.currentCalculus B.subtype k
          (liftedSphericalChain DB.lifted k z) := by
  obtain ⟨z,hz⟩ := projectedSphericalChain_surjective DB.simplex k P
  obtain ⟨w,hw⟩ := injective_geodesic_folding_chain DB.sphereAlgebra DG.sphereAlgebra Std.currentCalculus
    B.subtype Std.injectiveFolding DB.lifted DG.lifted Subtype.val_injective k z
  refine ⟨z,w,hz,?_,hw⟩
  apply Subtype.ext
  have he := homFold_projected_lift DB.M DG.M DB.algebra DG.algebra DB.sphereAlgebra DG.sphereAlgebra
    DB.simplex DG.simplex DB.lifted DG.lifted Std.currentCalculus DB.gluing DG.gluing B.subtype k z w hw
  rwa [hz] at he

end Paper28
