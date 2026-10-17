import Paper18.Category.FixedBoundaryModuleRegular
import Paper18.Category.DrinfeldBasic

/-! # Actual central objects acting as strong module endofunctors

The module lineator is the actual action of the half-braiding, conjugated
by the actual action associators. No pivotal or semisimplicity structure
is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.ModuleAlphaInduction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]

/-- The action pentagon, solved for the action of an associator. -/
@[reassoc] theorem associator_action_hom (X Y Z : C) (m : M) :
    (α_ X Y Z).hom ⊵ₗ m =
      (αₗ (X ⊗ Y) Z m).hom ≫ (αₗ X Y (Z ⊙ₗ m)).hom ≫
        X ⊴ₗ (αₗ Y Z m).inv ≫ (αₗ X (Y ⊗ Z) m).inv := by
  apply (cancel_mono ((αₗ X (Y ⊗ Z) m).hom ≫ X ⊴ₗ (αₗ Y Z m).hom)).mp
  simp only [Category.assoc, Iso.inv_hom_id_assoc, actionHomRight_inv_hom,
    Category.comp_id]
  exact associator_actionHom X Y Z m

/-- The inverse action pentagon in the form used by the actual lineator. -/
@[reassoc] theorem associator_action_inv (X Y Z : C) (m : M) :
    (α_ X Y Z).inv ⊵ₗ m =
      (αₗ X (Y ⊗ Z) m).hom ≫ X ⊴ₗ (αₗ Y Z m).hom ≫
        (αₗ X Y (Z ⊙ₗ m)).inv ≫ (αₗ (X ⊗ Y) Z m).inv := by
  apply (cancel_mono ((α_ X Y Z).hom ⊵ₗ m)).mp
  simp only [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]
  rw [associator_action_hom]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, actionHomRight_hom_inv_assoc,
    Iso.hom_inv_id]

@[reassoc] theorem leftUnitor_action_inv (X : C) (m : M) :
    (λ_ X).inv ⊵ₗ m = (λₗ (X ⊙ₗ m)).inv ≫ (αₗ (𝟙_ C) X m).inv := by
  apply (cancel_mono ((λ_ X).hom ⊵ₗ m)).mp
  simp only [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]
  rw [leftUnitor_actionHom]
  simp

/-- The actual inverse module lineator for a central object. -/
def centralLineator (Z : Center C) (X : C) (m : M) :
    Z.1 ⊙ₗ (X ⊙ₗ m) ≅ X ⊙ₗ (Z.1 ⊙ₗ m) :=
  (αₗ Z.1 X m).symm ≪≫
    (MonoidalLeftAction.actionRight C m).mapIso (Z.2.β X) ≪≫ αₗ X Z.1 m

@[reassoc] theorem actionAssoc_hom_naturality_right (X Y : C) {m n : M} (f : m ⟶ n) :
    (X ⊗ Y) ⊴ₗ f ≫ (αₗ X Y n).hom =
      (αₗ X Y m).hom ≫ X ⊴ₗ Y ⊴ₗ f := by
  simpa only [tensorHom_id, id_whiskerRight, id_actionHom] using
    (actionAssocIso_hom_naturality (𝟙 X) (𝟙 Y) f)

@[reassoc] theorem actionAssoc_inv_naturality_right (X Y : C) {m n : M} (f : m ⟶ n) :
    X ⊴ₗ Y ⊴ₗ f ≫ (αₗ X Y n).inv =
      (αₗ X Y m).inv ≫ (X ⊗ Y) ⊴ₗ f := by
  simpa only [tensorHom_id, id_whiskerRight, id_actionHom] using
    (actionAssocIso_inv_naturality (𝟙 X) (𝟙 Y) f)

@[reassoc] theorem actionAssoc_inv_naturality_middle (X : C) {Y Z : C}
    (f : Y ⟶ Z) (m : M) :
    X ⊴ₗ f ⊵ₗ m ≫ (αₗ X Z m).inv =
      (αₗ X Y m).inv ≫ (X ◁ f) ⊵ₗ m := by
  simpa only [actionHom_id, id_actionHom, id_tensorHom] using
    (actionAssocIso_inv_naturality (𝟙 X) f (𝟙 m))

/-- The half-braiding naturality proves actual naturality in the acting object. -/
@[reassoc] theorem centralLineator_naturality_left (Z : Center C)
    {X Y : C} (f : X ⟶ Y) (m : M) :
    Z.1 ⊴ₗ f ⊵ₗ m ≫ (centralLineator Z Y m).hom =
      (centralLineator Z X m).hom ≫ f ⊵ₗ (Z.1 ⊙ₗ m) := by
  dsimp only [centralLineator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    actionRight_map]
  rw [← Category.assoc, actionAssoc_inv_naturality_middle]
  simp only [Category.assoc]
  rw [← comp_actionHomLeft_assoc, Z.2.naturality, comp_actionHomLeft]
  rw [actionHomLeft_action]
  simp

/-- The action bifunctor laws prove actual naturality in the module object. -/
@[reassoc] theorem centralLineator_naturality_right (Z : Center C)
    (X : C) {m n : M} (f : m ⟶ n) :
    Z.1 ⊴ₗ X ⊴ₗ f ≫ (centralLineator Z X n).hom =
      (centralLineator Z X m).hom ≫ X ⊴ₗ Z.1 ⊴ₗ f := by
  dsimp only [centralLineator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    actionRight_map]
  rw [← Category.assoc, actionAssoc_inv_naturality_right]
  simp only [Category.assoc]
  rw [action_exchange_assoc, actionAssoc_hom_naturality_right]

/-- The actual half-braiding hexagon and the actual action pentagon give
module associativity of the actual central lineator. -/
@[reassoc] theorem centralLineator_associativity (Z : Center C)
    (X Y : C) (m : M) :
    (centralLineator Z (X ⊗ Y) m).hom ≫ (αₗ X Y (Z.1 ⊙ₗ m)).hom =
      Z.1 ⊴ₗ (αₗ X Y m).hom ≫
        (centralLineator Z X (Y ⊙ₗ m)).hom ≫
          X ⊴ₗ (centralLineator Z Y m).hom := by
  dsimp only [centralLineator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    actionRight_map]
  rw [Z.2.monoidal]
  simp only [comp_actionHomLeft, associator_action_inv, associator_action_hom,
    whiskerRight_actionHomLeft, whiskerLeft_actionHomLeft, actionHomRight_comp,
    Category.assoc]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The half-braiding unit, forced by its hexagon, gives actual module
unitality of the actual lineator. -/
@[reassoc] theorem centralLineator_unitality (Z : Center C) (m : M) :
    (λₗ (Z.1 ⊙ₗ m)).inv =
      Z.1 ⊴ₗ (λₗ m).inv ≫ (centralLineator Z (𝟙_ C) m).hom := by
  dsimp only [centralLineator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    actionRight_map]
  rw [Drinfeld.halfBraiding_unit, comp_actionHomLeft, rightUnitor_actionHom,
    leftUnitor_action_inv]
  simp

/-- Every actual central object defines an actual oplax module endofunctor.
All its inverse lineators are actual isomorphisms. -/
def centralOplaxLeftLinear (Z : Center C) :
    (MonoidalLeftAction.actionLeft M Z.1).OplaxLeftLinear C where
  δₗ X m := (centralLineator Z X m).hom
  δₗ_naturality_left := centralLineator_naturality_left Z
  δₗ_naturality_right := centralLineator_naturality_right Z
  δₗ_associativity := centralLineator_associativity Z
  δₗ_unitality_inv := centralLineator_unitality Z

end Paper18.Category.ModuleAlphaInduction
