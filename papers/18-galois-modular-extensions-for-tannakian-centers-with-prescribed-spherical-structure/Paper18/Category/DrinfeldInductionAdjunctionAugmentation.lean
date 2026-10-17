import Paper18.Category.DrinfeldInductionAdjunctionUnit

/-!
# Actual descent of the central-induction augmentation

The dinatural family is descended using the proved coend. The unit-component
normalization gives an actual left inverse and verifies the Hom-map direction.
Centrality of the descended map will be checked against the constructed
induction half-braiding, rather than assumed as adjunction data.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (J : PivotalStructure C) (S : FiniteSemisimpleSkeleton C ι)

/-- Descend the actual dinatural augmentation maps through the actual
induction coend. -/
def inductionAugmentation {X : C} (Z : Center C) (f : X ⟶ Z.1) :
    inductionUnderlying S X ⟶ Z.1 :=
  letI := inductionHasCoend S X
  coend.desc (inductionAugmentationComponent J Z f)
    (fun _ _ g => inductionAugmentationComponent_dinatural J Z f g)

@[reassoc (attr := simp)]
lemma inductionι_augmentation {X : C} (Z : Center C) (f : X ⟶ Z.1) (T : C) :
    inductionι S X T ≫ inductionAugmentation J S Z f =
      inductionAugmentationComponent J Z f T := by
  letI := inductionHasCoend S X
  exact coend.ι_desc _ _ T

/-- The prospective adjunction unit is an actual underlying morphism
coming from the tensor-unit coend component. -/
def inductionAdjunctionUnit (X : C) : X ⟶ inductionUnderlying S X :=
  inductionAdjunctionUnitComponent J X ≫ inductionι S X (𝟙_ C)

/-- The actual augmentation recovers the original map after the unit. -/
@[reassoc (attr := simp)]
lemma inductionAdjunctionUnit_augmentation {X : C} (Z : Center C) (f : X ⟶ Z.1) :
    inductionAdjunctionUnit J S X ≫ inductionAugmentation J S Z f = f := by
  rw [inductionAdjunctionUnit, Category.assoc, inductionι_augmentation]
  exact inductionAdjunctionUnitComponent_augmentation J Z f

/-- Hence the map from underlying Hom into coend Hom is injective, with an
explicit proved left inverse. This does not assume an adjunction. -/
lemma inductionAugmentation_injective {X : C} (Z : Center C) :
    Function.Injective (inductionAugmentation J S Z : (X ⟶ Z.1) → _) := by
  intro f g h
  have h' := congrArg (fun k => inductionAdjunctionUnit J S X ≫ k) h
  simpa only [inductionAdjunctionUnit_augmentation] using h'

/-- Every underlying central object is an actual retract of its induction
object through the actual augmentation. -/
def inductionAugmentationRetract (Z : Center C) : Retract Z.1 (inductionUnderlying S Z.1) where
  i := inductionAdjunctionUnit J S Z.1
  r := inductionAugmentation J S Z (𝟙 Z.1)
  retract := inductionAdjunctionUnit_augmentation J S Z (𝟙 Z.1)

lemma inductionAugmentation_add {X : C} (Z : Center C) (f g : X ⟶ Z.1) :
    inductionAugmentation J S Z (f + g) =
      inductionAugmentation J S Z f + inductionAugmentation J S Z g := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  simp only [Preadditive.comp_add, inductionι_augmentation,
    inductionAugmentationComponent, MonoidalPreadditive.whiskerLeft_add, MonoidalPreadditive.add_whiskerRight, Preadditive.add_comp]

lemma inductionAugmentation_smul {X : C} (Z : Center C) (c : ℂ) (f : X ⟶ Z.1) :
    inductionAugmentation J S Z (c • f) = c • inductionAugmentation J S Z f := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  simp only [Linear.comp_smul, inductionι_augmentation, inductionAugmentationComponent,
    MonoidalLinear.whiskerLeft_smul, MonoidalLinear.smul_whiskerRight, Linear.smul_comp]

/-- The actual augmentation is linear on underlying Hom spaces. -/
def inductionAugmentationLinearMap {X : C} (Z : Center C) :
    (X ⟶ Z.1) →ₗ[ℂ] (inductionUnderlying S X ⟶ Z.1) where
  toFun := inductionAugmentation J S Z
  map_add' := inductionAugmentation_add J S Z
  map_smul' := inductionAugmentation_smul J S Z

end Paper18.Category.Drinfeld
