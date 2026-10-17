import Paper18.Category.RepresentationDimension
import Paper18.Category.PivotalBalancing
import Paper18.Category.SphericalComparisonPositive

/-! # The actual canonical pivotal structure in symmetric rigid categories -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
universe v u
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [SymmetricCategory C]

/-- In a symmetric category the actual Drinfeld comparison is monoidal,
so its actual chosen-dual maps define the canonical pivotal structure. -/
def symmetricPivotal : PivotalStructure C where
  j := drinfeldNatIso
  unit := drinfeldIso_unit
  tensor X Y := by
    have h := drinfeldIso_tensor X Y
    simpa only [doubleBraiding, Iso.trans_hom, SymmetricCategory.symmetry, id_comp] using h

lemma symmetricPivotal_leftEvaluation (X : C) :
    symmetricPivotal.leftEvaluation X = (β_ X (dual C X)).hom ≫ ε_ X (dual C X) :=
  drinfeldIso_evaluation X

@[simp] lemma symmetricPivotal_twist (X : C) :
    (symmetricPivotal.twistIso X).hom = 𝟙 X :=
  (drinfeldIso X).hom_inv_id

lemma symmetricPivotal_leftCoevaluation (X : C) :
    symmetricPivotal.leftCoevaluation X =
      η_ X (dual C X) ≫ (β_ (dual C X) X).inv := by
  change η_ (dual C X) (dual C (dual C X)) ≫ dual C X ◁ (drinfeldIso X).inv = _
  rw [← drinfeldIso_coevaluation]
  simp only [assoc, ← whiskerLeft_comp, Iso.hom_inv_id, whiskerLeft_id, comp_id]

/-- Equality of actual left and right traces comes from naturality of the
ordinary symmetric crossing, with no dimension assignment assumed. -/
lemma symmetricPivotal_spherical : (symmetricPivotal (C := C)).Spherical := by
  intro X f
  dsimp only [PivotalStructure.leftTrace, PivotalStructure.rightTrace]
  rw [symmetricPivotal_leftCoevaluation, symmetricPivotal_leftEvaluation]
  rw [← SymmetricCategory.braiding_swap_eq_inv_braiding]
  simp only [assoc]
  rw [← braiding_naturality_left_assoc]

namespace Representation
variable {G : Type} [Group G]

/-- The actual canonical pivotal identification for finite-dimensional
representations, using their native chosen rigid duals and ordinary flip. -/
abbrev pivotalStructure : PivotalStructure (FDRep ℂ G) := symmetricPivotal

@[simp] lemma pivotalStructure_twist (V : FDRep ℂ G) :
    ((pivotalStructure (G := G)).twistIso V).hom = 𝟙 V := symmetricPivotal_twist V

lemma pivotalStructure_spherical : (pivotalStructure (G := G)).Spherical :=
  symmetricPivotal_spherical

end Representation
end Paper18.Category
