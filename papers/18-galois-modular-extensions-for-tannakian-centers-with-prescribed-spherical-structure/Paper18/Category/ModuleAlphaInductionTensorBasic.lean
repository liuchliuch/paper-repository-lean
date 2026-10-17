import Paper18.Category.ModuleAlphaInductionBasic

/-! # Tensor and unit coherence of the actual central module action -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.ModuleAlphaInduction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]

/-- The tensor half-braiding makes the actual action associator a module
natural transformation between the actual central module endofunctors. -/
@[reassoc] theorem centralLineator_tensor (Z W : Center C) (X : C) (m : M) :
    (αₗ Z.1 W.1 (X ⊙ₗ m)).inv ≫ (centralLineator (Z ⊗ W) X m).hom =
      Z.1 ⊴ₗ (centralLineator W X m).hom ≫
        (centralLineator Z X (W.1 ⊙ₗ m)).hom ≫ X ⊴ₗ (αₗ Z.1 W.1 m).inv := by
  dsimp only [centralLineator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    actionRight_map]
  change (αₗ Z.1 W.1 (X ⊙ₗ m)).inv ≫ (αₗ (Z.1 ⊗ W.1) X m).inv ≫
    (((α_ Z.1 W.1 X).hom ≫ Z.1 ◁ (W.2.β X).hom ≫
      (α_ Z.1 X W.1).inv ≫ (Z.2.β X).hom ▷ W.1 ≫ (α_ X Z.1 W.1).hom) ⊵ₗ m) ≫
      (αₗ X (Z.1 ⊗ W.1) m).hom = _
  simp only [comp_actionHomLeft, associator_action_inv, associator_action_hom,
    whiskerRight_actionHomLeft, whiskerLeft_actionHomLeft, actionHomRight_comp,
    Category.assoc]
  simp only [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

/-- The central unit's half-braiding makes the actual action unitor a
module natural transformation. -/
@[reassoc] theorem centralLineator_unit (X : C) (m : M) :
    (λₗ (X ⊙ₗ m)).inv ≫ (centralLineator (𝟙_ (Center C)) X m).hom =
      X ⊴ₗ (λₗ m).inv := by
  dsimp only [centralLineator, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom,
    actionRight_map]
  rw [Center.tensorUnit_β]
  change (λₗ (X ⊙ₗ m)).inv ≫ (αₗ (𝟙_ C) X m).inv ≫
    (((λ_ X).hom ≫ (ρ_ X).inv) ⊵ₗ m) ≫ (αₗ X (𝟙_ C) m).hom = _
  rw [comp_actionHomLeft, leftUnitor_actionHom]
  have hρ : (ρ_ X).inv ⊵ₗ m =
      X ⊴ₗ (λₗ m).inv ≫ (αₗ X (𝟙_ C) m).inv := by
    apply (cancel_mono ((ρ_ X).hom ⊵ₗ m)).mp
    rw [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft, rightUnitor_actionHom]
    simp
  rw [hρ]
  simp

end Paper18.Category.ModuleAlphaInduction
