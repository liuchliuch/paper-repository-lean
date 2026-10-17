import Paper18.Category.DrinfeldInductionAdjunction
import Paper18.Category.DrinfeldInductionFunctor

/-! # The actual left adjunction of central induction and forgetful functor -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- Naturality of the actual coend augmentation in its middle input. -/
lemma inductionAugmentation_precomp {X Y : C} (Z : Center C) (g : X ⟶ Y) (f : Y ⟶ Z.1) :
    inductionAugmentation J S Z (g ≫ f) =
      inductionUnderlyingMap S g ≫ inductionAugmentation J S Z f := by
  letI := inductionHasCoend S X
  apply coend.hom_ext
  intro T
  change inductionι S X T ≫ _ = inductionι S X T ≫ _
  rw [inductionι_augmentation, inductionUnderlyingMap_ι_assoc, inductionι_augmentation]
  simp only [inductionAugmentationComponent, whiskerLeft_comp, comp_whiskerRight, assoc]

/-- The actual central induction functor is left adjoint to the actual
forgetful functor. All Hom equivalences and naturality equations are derived. -/
def inductionAdjunction : inductionFunctor S J ⊣ Center.forget C :=
  Adjunction.mkOfHomEquiv
    { homEquiv := inductionHomEquiv S J
      homEquiv_naturality_left_symm := fun f g => by
        apply Center.ext
        exact inductionAugmentation_precomp S J _ f g
      homEquiv_naturality_right := fun f g =>
        inductionHomEquiv_naturality_right S J f g }

@[simp] lemma inductionAdjunction_homEquiv (X : C) (Z : Center C) :
    (inductionAdjunction S J).homEquiv X Z = inductionHomEquiv S J X Z := by
  unfold inductionAdjunction
  rw [Adjunction.mkOfHomEquiv_homEquiv]

@[simp] lemma inductionAdjunction_unit_app (X : C) :
    (inductionAdjunction S J).unit.app X = inductionAdjunctionUnit J S X := by
  simp [inductionAdjunction, Adjunction.mkOfHomEquiv, inductionHomEquiv]

@[simp] lemma inductionAdjunction_counit_app (Z : Center C) :
    (inductionAdjunction S J).counit.app Z = inductionCounit S J Z := rfl

instance inductionFunctor_isLeftAdjoint : (inductionFunctor S J).IsLeftAdjoint :=
  (inductionAdjunction S J).isLeftAdjoint

/-- The actual forgetful functor has the proved central-induction left adjoint. -/
def centerForgetIsRightAdjoint : (Center.forget C).IsRightAdjoint :=
  (inductionAdjunction S J).isRightAdjoint

/-- The actual counit of this adjunction is epi. -/
instance inductionAdjunction_counit_epi (Z : Center C) :
    Epi ((inductionAdjunction S J).counit.app Z) :=
  inductionCounit_epi S J Z

end Paper18.Category.Drinfeld
