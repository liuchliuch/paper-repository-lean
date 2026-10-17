import Paper18.Category.DrinfeldInductionAdjunctionHom
import Paper18.Category.DrinfeldInduction
import Paper18.Category.DrinfeldLinear

/-!
# Actual universal Hom equivalence for central induction

The counit is an actual morphism in the Drinfeld center. Its universal
property is proved from the coend construction and generation by the unit.
The Hom equivalence and its complex linear structure are conclusions.
-/
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

/-- The actual augmentation is a central morphism; its commutation equation
was proved by actual coend descent and pivotal cap calculations. -/
def inductionAugmentationHom {X : C} (Z : Center C) (f : X ⟶ Z.1) :
    inductionObj S J X ⟶ Z where
  f := inductionAugmentation J S Z f
  comm U := inductionAugmentation_central J S Z f U

@[simp] lemma inductionAugmentationHom_f {X : C} (Z : Center C) (f : X ⟶ Z.1) :
    (inductionAugmentationHom S J Z f).f = inductionAugmentation J S Z f := rfl

/-- The universal correspondence for the actual central induction object.
This establishes the left-adjoint orientation. -/
def inductionHomEquiv (X : C) (Z : Center C) :
    (inductionObj S J X ⟶ Z) ≃ (X ⟶ Z.1) where
  toFun h := inductionAdjunctionUnit J S X ≫ h.f
  invFun := inductionAugmentationHom S J Z
  left_inv h := by
    apply Center.ext
    exact inductionAugmentation_recover J S Z h.f (fun U => h.comm U)
  right_inv f := inductionAdjunctionUnit_augmentation J S Z f

@[simp] lemma inductionHomEquiv_apply {X : C} {Z : Center C} (h : inductionObj S J X ⟶ Z) :
    inductionHomEquiv S J X Z h = inductionAdjunctionUnit J S X ≫ h.f := rfl

@[simp] lemma inductionHomEquiv_symm_apply {X : C} (Z : Center C) (f : X ⟶ Z.1) :
    (inductionHomEquiv S J X Z).symm f = inductionAugmentationHom S J Z f := rfl

/-- The actual universal Hom correspondence is complex linear. -/
def inductionHomLinearEquiv (X : C) (Z : Center C) :
    (inductionObj S J X ⟶ Z) ≃ₗ[ℂ] (X ⟶ Z.1) where
  toEquiv := inductionHomEquiv S J X Z
  map_add' f g := by
    change inductionAdjunctionUnit J S X ≫ (f.f + g.f) =
      inductionAdjunctionUnit J S X ≫ f.f + inductionAdjunctionUnit J S X ≫ g.f
    simp only [Preadditive.comp_add]
  map_smul' c f := by
    change inductionAdjunctionUnit J S X ≫ (c • f.f) =
      c • (inductionAdjunctionUnit J S X ≫ f.f)
    simp only [Linear.comp_smul]

/-- The universal Hom equivalence is natural in the actual central target. -/
lemma inductionHomEquiv_naturality_right {X : C} {Z W : Center C}
    (h : inductionObj S J X ⟶ Z) (g : Z ⟶ W) :
    inductionHomEquiv S J X W (h ≫ g) = inductionHomEquiv S J X Z h ≫ g.f := by
  simp only [inductionHomEquiv_apply, Center.comp_f, assoc]

/-- The actual adjunction counit at a central object. -/
def inductionCounit (Z : Center C) : inductionObj S J Z.1 ⟶ Z :=
  inductionAugmentationHom S J Z (𝟙 Z.1)

/-- The underlying counit has the actual unit as a section. -/
@[reassoc (attr := simp)]
lemma inductionAdjunctionUnit_counit (Z : Center C) :
    inductionAdjunctionUnit J S Z.1 ≫ (inductionCounit S J Z).f = 𝟙 Z.1 :=
  inductionAdjunctionUnit_augmentation J S Z (𝟙 Z.1)

/-- The actual central counit is an epimorphism, as witnessed by its
underlying split epimorphism and the faithful forgetful functor. -/
instance inductionCounit_epi (Z : Center C) : Epi (inductionCounit S J Z) where
  left_cancellation {W} f g h := by
    apply Center.ext
    have h' := congrArg (fun k : inductionObj S J Z.1 ⟶ W =>
      inductionAdjunctionUnit J S Z.1 ≫ k.f) h
    simpa only [Center.comp_f, ← assoc, inductionAdjunctionUnit_counit,
      id_comp] using h'

end Paper18.Category.Drinfeld
