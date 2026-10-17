import Paper18.Category.DrinfeldInductionCoend
import Paper18.Category.PivotalDuality

/-!
# Actual augmentation components for central induction

A morphism from `X` to the underlying object of a central object `Z`
produces maps `(T ⊗ X) ⊗ T* → Z` using the inverse half-braiding and the
prescribed pivotal left evaluation. Dinaturality is proved from actual
half-braiding naturality and dual-evaluation naturality.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Opposite
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (J : PivotalStructure C)

/-- Naturality of the actual pivotal left evaluation against the chosen
right-dual map. -/
lemma pivotalLeftEvaluation_naturality {T U : C} (f : T ⟶ U) :
    (f ▷ Uᘁ) ≫ J.leftEvaluation U =
      (T ◁ rightAdjointMate f) ≫ J.leftEvaluation T := by
  dsimp only [PivotalStructure.leftEvaluation]
  rw [← comp_whiskerRight_assoc]
  have hn := J.j.hom.naturality f
  simp only [Functor.id_map] at hn
  rw [hn]
  dsimp only [doubleDualFunctor, dualMap]
  rw [comp_whiskerRight_assoc, rightAdjointMate_comp_evaluation]
  rw [whisker_exchange_assoc]

/-- Closing the inverse half-braiding by the actual pivotal cap. -/
def inductionAugmentationCap (Z : Center C) (T : C) : (T ⊗ Z.1) ⊗ Tᘁ ⟶ Z.1 :=
  (Z.2.β T).inv ▷ Tᘁ ≫ (α_ Z.1 T Tᘁ).hom ≫
    Z.1 ◁ J.leftEvaluation T ≫ (ρ_ Z.1).hom

/-- The actual candidate counit component associated to `f : X → U Z`.
Its direction is from induction to the central object. -/
def inductionAugmentationComponent {X : C} (Z : Center C) (f : X ⟶ Z.1) (T : C) :
    (T ⊗ X) ⊗ Tᘁ ⟶ Z.1 :=
  (T ◁ f) ▷ Tᘁ ≫ inductionAugmentationCap J Z T

/-- The actual cap family is dinatural in its indexing object. -/
lemma inductionAugmentationCap_dinatural (Z : Center C) {T U : C} (f : T ⟶ U) :
    ((T ⊗ Z.1) ◁ rightAdjointMate f) ≫ inductionAugmentationCap J Z T =
      ((f ▷ Z.1) ▷ Uᘁ) ≫ inductionAugmentationCap J Z U := by
  calc
    _ = 𝟙 ((T ⊗ Z.1) ⊗ Uᘁ) ⊗≫
        (Z.2.β T).inv ▷ Uᘁ ⊗≫ Z.1 ◁ ((T ◁ rightAdjointMate f) ≫
          J.leftEvaluation T) ⊗≫ 𝟙 Z.1 := by
      dsimp [inductionAugmentationCap]
      rw [whisker_exchange_assoc]
      monoidal
    _ = 𝟙 ((T ⊗ Z.1) ⊗ Uᘁ) ⊗≫
        (Z.2.β T).inv ▷ Uᘁ ⊗≫ Z.1 ◁ ((f ▷ Uᘁ) ≫
          J.leftEvaluation U) ⊗≫ 𝟙 Z.1 := by
      rw [← pivotalLeftEvaluation_naturality J f]
    _ = 𝟙 ((T ⊗ Z.1) ⊗ Uᘁ) ⊗≫
        ((Z.2.β T).inv ≫ Z.1 ◁ f) ▷ Uᘁ ⊗≫
          Z.1 ◁ J.leftEvaluation U ⊗≫ 𝟙 Z.1 := by monoidal
    _ = _ := by
      rw [← halfBraiding_inv_naturality Z.2 f]
      dsimp [inductionAugmentationCap]
      monoidal

/-- The actual augmentation components satisfy exactly the induction
coend's dinaturality equation. -/
lemma inductionAugmentationComponent_dinatural {X : C} (Z : Center C) (f : X ⟶ Z.1)
    {T U : C} (g : T ⟶ U) :
    ((T ⊗ X) ◁ rightAdjointMate g) ≫ inductionAugmentationComponent J Z f T =
      ((g ▷ X) ▷ Uᘁ) ≫ inductionAugmentationComponent J Z f U := by
  unfold inductionAugmentationComponent
  rw [whisker_exchange_assoc]
  rw [inductionAugmentationCap_dinatural J Z g]
  rw [← comp_whiskerRight_assoc, whisker_exchange, comp_whiskerRight_assoc]

end Paper18.Category.Drinfeld
