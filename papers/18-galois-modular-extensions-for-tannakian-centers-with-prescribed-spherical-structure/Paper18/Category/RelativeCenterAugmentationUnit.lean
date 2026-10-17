import Paper18.Category.RelativeCenterAveraging

/-! # Actual relative augmentation is detected by the ambient unit insertion -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.RelativeCenter
open Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {P : ObjectProperty C} [P.IsMonoidal] (J : PivotalStructure C)

/-- Closing the actual unit component returns exactly the original map.
This verifies the prospective left-adjoint orientation by an actual equation. -/
lemma inductionAdjunctionUnitComponent_augmentation {X : C} (Z : RelativeCenter P) (f : X ⟶ Z.1) :
    inductionAdjunctionUnitComponent J X ≫ augmentationComponent J Z f (𝟙_ C) (ObjectProperty.prop_unit P) = f := by
  have hb : Z.2.β (𝟙_ C) (ObjectProperty.prop_unit P) = ρ_ Z.1 ≪≫ (λ_ Z.1).symm := by
    apply Iso.ext
    exact Z.2.unit
  calc
    _ = (ρ_ X).inv ≫ X ◁ (pivotalUnitDualIso J).inv ≫
        f ▷ ((𝟙_ C)ᘁ) ≫ Z.1 ◁ (pivotalUnitDualIso J).hom ≫ (ρ_ Z.1).hom := by
      dsimp [inductionAdjunctionUnitComponent, augmentationComponent,
        augmentationCap]
      rw [hb, ← pivotalUnitDualIso_evaluation J]
      simp only [Iso.trans_inv, Iso.symm_inv]
      monoidal
    _ = (ρ_ X).inv ≫ f ▷ (𝟙_ C) ≫ Z.1 ◁
        ((pivotalUnitDualIso J).inv ≫ (pivotalUnitDualIso J).hom) ≫ (ρ_ Z.1).hom := by
      rw [← whisker_exchange_assoc, ← whiskerLeft_comp_assoc]
      simp
    _ = f := by simp

variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C] [Simple (𝟙_ C)] [BraidedCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [IsAdditiveFullProperty P]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

@[reassoc]
lemma adjunctionUnit_augmentation {X : C} (Z : RelativeCenter P) (f : X ⟶ Z.1) :
    inductionAdjunctionUnit J S X ≫ augmentation S J Z f = f := by
  rw [inductionAdjunctionUnit, assoc,
    inductionι_augmentation_of_property S J Z f _ (ObjectProperty.prop_unit P),
    inductionAdjunctionUnitComponent_augmentation]

end Paper18.Category.RelativeCenter
