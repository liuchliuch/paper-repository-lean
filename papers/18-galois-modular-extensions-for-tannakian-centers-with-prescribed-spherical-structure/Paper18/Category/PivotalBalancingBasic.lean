import Paper18.Category.RadfordBraided
import Paper18.Category.SphericalComparison

/-!
# The actual twist induced by a pivotal identification

The twist is the quotient of the given pivotal natural isomorphism by the
canonical Drinfeld comparison. In particular neither its components nor their
scalars on simple objects are extra input data.
-/
noncomputable section
open Classical
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [BraidedCategory C]

namespace PivotalStructure
variable (J : PivotalStructure C)

/-- The actual twist natural isomorphism induced by the pivotal structure. -/
def twistNatIso : 𝟭 C ≅ 𝟭 C := J.j ≪≫ (drinfeldNatIso (C := C)).symm

/-- The twist automorphism of an actual object. -/
def twistIso (X : C) : X ≅ X := J.twistNatIso.app X

@[simp] lemma twistIso_hom (X : C) :
    (J.twistIso X).hom = J.j.hom.app X ≫ (drinfeldIso X).inv := rfl

@[simp] lemma twistIso_inv (X : C) :
    (J.twistIso X).inv = (drinfeldIso X).hom ≫ J.j.inv.app X := rfl

lemma twist_naturality {X Y : C} (f : X ⟶ Y) :
    f ≫ (J.twistIso Y).hom = (J.twistIso X).hom ≫ f :=
  J.twistNatIso.hom.naturality f

lemma twist_comp_drinfeld (X : C) :
    (J.twistIso X).hom ≫ (drinfeldIso X).hom = J.j.hom.app X := by
  simp only [twistIso_hom, assoc, Iso.inv_hom_id, comp_id]

/-- The twist converts the braided evaluation into the actual pivotal cap. -/
lemma twist_evaluation (X : C) :
    (J.twistIso X).hom ▷ dual C X ≫ (β_ X (dual C X)).hom ≫ ε_ X (dual C X) =
      J.leftEvaluation X := by
  rw [← drinfeldIso_evaluation, ← comp_whiskerRight_assoc, J.twist_comp_drinfeld]
  rfl

/-- Closing this actual cap computes the actual pivotal dimension. -/
lemma rightDimension_twist (X : C) :
    J.rightDimension X = η_ X (dual C X) ≫
      (J.twistIso X).hom ▷ dual C X ≫ (β_ X (dual C X)).hom ≫ ε_ X (dual C X) := by
  rw [J.twist_evaluation]
  simp only [rightDimension, rightTrace, id_whiskerRight, id_comp]

variable [Preadditive C] [Linear ℂ C] [HasKernels C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]

/-- The twist scalar on an actual simple, extracted by Schur's lemma. -/
def twistScalar (X : C) [Simple X] : ℂ := TensorAutomorphism.scalar J.twistNatIso X

lemma twistScalar_spec (X : C) [Simple X] :
    J.twistScalar X • 𝟙 X = (J.twistIso X).hom :=
  TensorAutomorphism.scalar_spec J.twistNatIso X

lemma twistScalar_ne_zero (X : C) [Simple X] : J.twistScalar X ≠ 0 :=
  TensorAutomorphism.scalar_ne_zero J.twistNatIso X

lemma twistScalar_iso {X Y : C} [Simple X] [Simple Y] (e : X ≅ Y) :
    J.twistScalar X = J.twistScalar Y := TensorAutomorphism.scalar_iso J.twistNatIso e

end PivotalStructure
end Paper18.Category
