import Paper18.Category.RelativeTensorCentralFreeMonoidal
import Paper18.Category.DrinfeldLinear

/-! # Actual free central morphisms and ambient positive-negative morphisms -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open CategoryTheory.BraidedCategory
open scoped MonObj
universe v u
namespace Paper18.Category.RelativeTensor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [HasCoequalizers C] {A : C} [MonObj A] [IsCommMonObj A]

@[reassoc]
theorem freeCentralIso_tensorFreeIso (X : C) (M : Mod_ C A) :
    (freeCentralIso X M).hom.hom ≫ (tensorFreeIso M X).hom.hom =
      (leftFreeIso X M).hom.hom := by
  have h : (freeCentralIso X M).hom ≫ (tensorFreeIso M X).hom =
      (leftFreeIso X M).hom := by
    dsimp only [freeCentralIso, Iso.trans_hom, Iso.symm_hom]
    rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg Mod_.Hom.hom h

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem leftFreeLinearHom_freeUnit_right (Y Z : C) :
    ((InternalModule.free A Y).X ◁ freeUnit Z) ≫
        (leftFreeLinearHom Y (InternalModule.free A Z)).hom =
      (α_ A Y Z).hom ≫ (A ◁ (β_ Y Z).hom) ≫ (α_ A Z Y).inv := by
  have hu : (A ◁ freeUnit (A := A) Z) ≫ γ[A,(InternalModule.free A Z).X] = 𝟙 _ :=
    congrArg Mod_.Hom.hom (freeLift_freeUnit (A := A) Z)
  rw [leftFreeLinearHom_hom]
  erw [associator_naturality_right_assoc]
  erw [← whiskerLeft_comp_assoc, braiding_naturality_right,
    whiskerLeft_comp_assoc, associator_inv_naturality_middle_assoc]
  rw [← comp_whiskerRight, hu, id_whiskerRight, Category.comp_id]

omit [RightRigidCategory C] [HasCoequalizers C] [IsCommMonObj A] in
@[reassoc]
theorem tensorFreeMap_freeUnit_left (Z Y : C) :
    (freeUnit (A := A) Z ▷ (InternalModule.free A Y).X) ≫
        tensorFreeMap (InternalModule.free A Z) Y =
      (α_ Z A Y).inv ≫ (β_ Z A).hom ▷ Y := by
  unfold tensorFreeMap
  erw [associator_inv_naturality_left_assoc, ← comp_whiskerRight,
    freeUnit_rightAction]

/-- The actual centrality equation, evaluated on two actual free
algebra-unit generators. -/
@[reassoc]
theorem centralFreeHom_generator_equation {X Y : C}
    (f : (centralFreeFunctor (A := A)).obj X ⟶ (centralFreeFunctor (A := A)).obj Y)
    (Z : C) :
    ((freeUnit X ≫ f.f.hom) ▷ Z) ≫ (α_ A Y Z).hom ≫
        (A ◁ (β_ Y Z).hom) ≫ (α_ A Z Y).inv =
      (β_ X Z).hom ≫ (Z ◁ (freeUnit X ≫ f.f.hom)) ≫
        (α_ Z A Y).inv ≫ (β_ Z A).hom ▷ Y := by
  have h := congrArg (fun k =>
      (freeUnit (A := A) X ⊗ₘ freeUnit (A := A) Z) ≫
        π (InternalModule.free A X) (InternalModule.free A Z) ≫ k.hom ≫
        (tensorFreeIso (InternalModule.free A Z) Y).hom.hom)
    (f.comm (InternalModule.free A Z))
  dsimp only [centralFreeFunctor, centralFreeObj, freeHalfBraiding] at h
  simp only [Mod_.comp_hom', Category.assoc] at h
  erw [π_whiskerRight_assoc, tensorHom_comp_whiskerRight_assoc,
    freeCentralIso_tensorFreeIso, π_leftFreeHom] at h
  rw [MonoidalCategory.tensorHom_def, Category.assoc,
    leftFreeLinearHom_freeUnit_right] at h
  rw [MonoidalCategory.tensorHom_def', Category.assoc,
    freeUnit_π_freeCentralIso_assoc, π_whiskerLeft_assoc,
    ← whiskerLeft_comp_assoc] at h
  rw [braiding_naturality_right_assoc] at h
  erw [π_tensorFreeHom] at h
  erw [← whisker_exchange_assoc, tensorFreeMap_freeUnit_left] at h
  exact h

/-- Evaluate an actual central free morphism on the algebra-unit generators.
Its centrality is precisely a morphism from the positive ambient image into
the product of the negative algebra image and positive target image. -/
def centralFreeHomAmbient {X Y : C}
    (f : (centralFreeFunctor (A := A)).obj X ⟶ (centralFreeFunctor (A := A)).obj Y) :
    (Drinfeld.positive C).obj X ⟶
      (Drinfeld.negative C).obj A ⊗ (Drinfeld.positive C).obj Y where
  f := freeUnit X ≫ f.f.hom
  comm Z := by
    simp only [Center.tensor_β, Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom,
      whiskerRightIso_hom]
    change ((freeUnit X ≫ f.f.hom) ▷ Z) ≫ (α_ A Y Z).hom ≫
        (A ◁ (β_ Y Z).hom) ≫ (α_ A Z Y).inv ≫
        (β_ Z A).inv ▷ Y ≫ (α_ Z A Y).hom =
      (β_ X Z).hom ≫ Z ◁ (freeUnit X ≫ f.f.hom)
    rw [centralFreeHom_generator_equation_assoc]
    rw [← comp_whiskerRight_assoc, Iso.hom_inv_id, id_whiskerRight,
      Category.id_comp, Iso.inv_hom_id, Category.comp_id]

/-- The ambient positive-negative comparison remembers the entire actual
central free morphism. -/
theorem centralFreeHomAmbient_injective (X Y : C) :
    Function.Injective (centralFreeHomAmbient (A := A) (X := X) (Y := Y)) := by
  intro f g h
  apply Center.ext
  apply free_hom_ext
  exact congrArg Center.Hom.f h

section Linear
variable [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

/-- The actual central comparison is a complex-linear injection on Hom. -/
def centralFreeHomAmbientLinear (X Y : C) :
    ((centralFreeFunctor (A := A)).obj X ⟶ (centralFreeFunctor (A := A)).obj Y) →ₗ[ℂ]
      ((Drinfeld.positive C).obj X ⟶
        (Drinfeld.negative C).obj A ⊗ (Drinfeld.positive C).obj Y) where
  toFun := centralFreeHomAmbient
  map_add' f g := by
    apply Center.ext
    change freeUnit X ≫ (f + g).f.hom = freeUnit X ≫ f.f.hom + freeUnit X ≫ g.f.hom
    simp [Preadditive.comp_add]
  map_smul' r f := by
    apply Center.ext
    change freeUnit X ≫ (r • f).f.hom = r • (freeUnit X ≫ f.f.hom)
    simp

end Linear
end Paper18.Category.RelativeTensor
