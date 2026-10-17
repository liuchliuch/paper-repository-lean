import Paper18.Category.DrinfeldSemisimpleDiagram
import Paper18.Category.DrinfeldInductionHexagon

/-! # Actual right-transpose helpers for the central averaging slide -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.Drinfeld
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]

/-- The actual section component is the rigid right transpose of its
half-braiding, with no extra identification supplied. -/
lemma inductionSectionComponent_rightTranspose (Z : Center C) (A : C) :
    inductionSectionComponent Z A =
      tensorRightHomEquiv Z.1 A (dual C A) (A ⊗ Z.1) (Z.2.β A).hom := by
  rw [inductionSectionComponent_transpose]
  change _ = (ρ_ Z.1).inv ≫ Z.1 ◁ η_ A (dual C A) ≫
    (α_ Z.1 A (dual C A)).inv ≫ (Z.2.β A).hom ▷ dual C A
  monoidal

/-- Closing that actual transpose returns the original half-braiding. -/
lemma inductionSectionComponent_evaluation (Z : Center C) (A : C) :
    inductionSectionComponent Z A ▷ A ≫ (α_ (A ⊗ Z.1) (dual C A) A).hom ≫
      (A ⊗ Z.1) ◁ ε_ A (dual C A) ≫ (ρ_ (A ⊗ Z.1)).hom = (Z.2.β A).hom := by
  rw [inductionSectionComponent_rightTranspose]
  exact (tensorRightHomEquiv Z.1 A (dual C A) (A ⊗ Z.1)).symm_apply_apply _

/-- Close the last dual strand after the coherent outer reassociation. -/
def averagingSlideClose {K : C} (U B Z : C)
    (f : K ⟶ U ⊗ ((B ⊗ Z) ⊗ dual C B)) : K ⊗ B ⟶ U ⊗ (B ⊗ Z) :=
  (tensorRightHomEquiv K B (dual C B) (U ⊗ (B ⊗ Z))).symm
    (f ≫ (α_ U (B ⊗ Z) (dual C B)).inv)

/-- Its explicit cup-and-cap diagram. -/
lemma averagingSlideClose_eq {K : C} (U B Z : C)
    (f : K ⟶ U ⊗ ((B ⊗ Z) ⊗ dual C B)) :
    averagingSlideClose U B Z f =
      𝟙 (K ⊗ B) ⊗≫ f ▷ B ⊗≫
        (U ⊗ (B ⊗ Z)) ◁ ε_ B (dual C B) ⊗≫ 𝟙 (U ⊗ (B ⊗ Z)) := by
  change ((f ≫ (α_ U (B ⊗ Z) (dual C B)).inv) ▷ B) ≫
    (α_ (U ⊗ (B ⊗ Z)) (dual C B) B).hom ≫
      (U ⊗ (B ⊗ Z)) ◁ ε_ B (dual C B) ≫ (ρ_ (U ⊗ (B ⊗ Z))).hom = _
  monoidal

lemma averagingSlideClose_injective {K : C} (U B Z : C) :
    Function.Injective (averagingSlideClose (K := K) U B Z) := by
  intro f g h
  apply (cancel_mono (α_ U (B ⊗ Z) (dual C B)).inv).mp
  exact (tensorRightHomEquiv K B (dual C B) (U ⊗ (B ⊗ Z))).symm.injective h


/-- Naturality of actual right transposition in its dual-labelled strand. -/
lemma rightTransposeClose_dual {K L A B : C} (f : K ⟶ L ⊗ dual C A) (u : B ⟶ A) :
    (tensorRightHomEquiv K B (dual C B) L).symm (f ≫ L ◁ dualMap C u) =
      (K ◁ u) ≫ (tensorRightHomEquiv K A (dual C A) L).symm f := by
  calc
    _ = f ▷ B ≫ (α_ L (dual C A) B).hom ≫
        L ◁ (dualMap C u ▷ B ≫ ε_ B (dual C B)) ≫ (ρ_ L).hom := by
      change ((f ≫ L ◁ dualMap C u) ▷ B) ≫
        (α_ L (dual C B) B).hom ≫ L ◁ ε_ B (dual C B) ≫ (ρ_ L).hom = _
      monoidal
    _ = f ▷ B ≫ (α_ L (dual C A) B).hom ≫
        L ◁ ((dual C A ◁ u) ≫ ε_ A (dual C A)) ≫ (ρ_ L).hom := by
      rw [rightAdjointMate_comp_evaluation]
    _ = ((f ▷ B) ≫ (L ⊗ dual C A) ◁ u) ≫
        (α_ L (dual C A) A).hom ≫ L ◁ ε_ A (dual C A) ≫ (ρ_ L).hom := by monoidal
    _ = _ := by
      rw [← whisker_exchange]
      change _ = (K ◁ u) ≫ f ▷ A ≫ (α_ L (dual C A) A).hom ≫
        L ◁ ε_ A (dual C A) ≫ (ρ_ L).hom
      simp only [assoc]

/-- Naturality of actual right transposition in its unbent target. -/
lemma rightTransposeClose_comp {K L M A : C} (f : K ⟶ L ⊗ dual C A) (g : L ⟶ M) :
    (tensorRightHomEquiv K A (dual C A) M).symm (f ≫ g ▷ dual C A) =
      (tensorRightHomEquiv K A (dual C A) L).symm f ≫ g := by
  apply (tensorRightHomEquiv K A (dual C A) M).injective
  rw [Equiv.apply_symm_apply, tensorRightHomEquiv_naturality, Equiv.apply_symm_apply]

/-- The two actual matrix maps in the averaging slide become ordinary
precomposition and postcomposition after closing the last dual strand. -/
lemma averagingSlideClose_naturality {K A B : C} (U Z : C)
    (f : K ⟶ U ⊗ ((A ⊗ Z) ⊗ dual C A)) (u : B ⟶ A) (p : A ⟶ B) :
    averagingSlideClose U B Z
      (f ≫ U ◁ (((p ▷ Z) ▷ dual C A) ≫ (B ⊗ Z) ◁ dualMap C u)) =
      (K ◁ u) ≫ averagingSlideClose U A Z f ≫ U ◁ (p ▷ Z) := by
  have h : (f ≫ U ◁ (((p ▷ Z) ▷ dual C A) ≫ (B ⊗ Z) ◁ dualMap C u)) ≫
      (α_ U (B ⊗ Z) (dual C B)).inv =
      ((f ≫ (α_ U (A ⊗ Z) (dual C A)).inv) ≫
        (U ◁ (p ▷ Z)) ▷ dual C A) ≫ (U ⊗ (B ⊗ Z)) ◁ dualMap C u := by monoidal
  dsimp only [averagingSlideClose]
  rw [h, rightTransposeClose_dual, rightTransposeClose_comp]

end Paper18.Category.Drinfeld
