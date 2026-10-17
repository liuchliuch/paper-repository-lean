import Paper18.Category.DrinfeldCoendModulesActionComponent

/-! # The actual tensor identity of annular crossings -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.BraidedCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

/-- Half-braiding hexagons give the exact actual annular tensor identity. -/
lemma holonomy_tensor (Z : Center D) (Y X : D) :
    (holonomy Z (Y ⊗ X)).hom =
      (α_ Y X Z.1).hom ≫ Y ◁ (holonomy Z X).hom ≫
        Y ◁ (β_ X Z.1).hom ≫ (α_ Y Z.1 X).inv ≫
          (holonomy Z Y).hom ▷ X ≫ (α_ Y Z.1 X).hom ≫
            Y ◁ (β_ X Z.1).inv ≫ (α_ Y X Z.1).inv := by
  have he : Z.2.β (Y ⊗ X) =
      (α_ Z.1 Y X).symm ≪≫ whiskerRightIso (Z.2.β Y) X ≪≫
        α_ Y Z.1 X ≪≫ whiskerLeftIso Y (Z.2.β X) ≪≫ (α_ Y X Z.1).symm := by
    apply Iso.ext
    exact Z.2.monoidal Y X
  dsimp only [holonomy, Iso.trans_hom, Iso.symm_hom]
  rw [he, braiding_tensor_left_inv]
  simp only [Iso.trans_inv, Iso.symm_inv, whiskerRightIso_inv, whiskerLeftIso_inv,
    assoc, Iso.hom_inv_id_assoc, comp_whiskerRight, whiskerLeft_comp,
    Iso.inv_hom_id_assoc]
  have hc : Y ◁ (β_ X Z.1).inv ≫ Y ◁ (β_ X Z.1).hom = 𝟙 _ := by
    rw [← whiskerLeft_comp, Iso.inv_hom_id, whiskerLeft_id]
  simp only [reassoc_of% hc, id_comp]

end Paper18.Category.DrinfeldCoendModules
