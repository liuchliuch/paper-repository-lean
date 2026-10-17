import Paper18.Category.GraphPicardMoritaProductActionLift
import Paper18.Category.GraphPicardMoritaProductModel
import Paper18.Category.GraphPicardNativeMonoidalBasic
import Mathlib.CategoryTheory.Monoidal.Action.End

/-! # The actual remaining ambient action on the balanced-product model

Actual signed alpha induction consists of genuine strong module functors.
It therefore acts on actual algebra-module objects through the constructed
strong module lift. The resulting action is defined from an actual strong
monoidal functor, so its pentagon and triangle are derived.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalLeftAction MonoidalOpposite
open scoped MonObj MonoidalRightAction
universe v u vM uM
namespace Paper18.Category.GraphPicard.MoritaProduct
attribute [local instance] CategoryTheory.endofunctorMonoidalCategory
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  (A : C) [MonObj A]

/-- Genuine negative alpha induction followed by actual module transport
gives the actual remaining action functor. -/
def negativeLiftedActionFunctor : C ⥤ (Mod_ M A ⥤ Mod_ M A)ᴹᵒᵖ :=
  ModuleAlphaInduction.negativeMop C M ⋙ simultaneousMop (moduleLift C M A)

instance negativeLiftedActionFunctor_monoidal :
    (negativeLiftedActionFunctor C M A).Monoidal := by
  unfold negativeLiftedActionFunctor
  infer_instance

/-- Actual coherent action on actual internal modules. No action or
action-coherence conclusion is a field or additional premise. -/
def negativeLiftedAction : MonoidalLeftAction C (Mod_ M A) :=
  MonoidalLeftAction.actionOfMonoidalFunctorToEndofunctorMop
    (negativeLiftedActionFunctor C M A)

theorem negativeLiftedAction_obj (X : C) (P : Mod_ M A) :
    letI := negativeLiftedAction C M A
    (X ⊙ₗ P).X = X ⊙ₗ P.X := rfl

theorem negativeLiftedAction_map_right (X : C) {P Q : Mod_ M A} (f : P ⟶ Q) :
    letI := negativeLiftedAction C M A
    (X ⊴ₗ f).hom = X ⊴ₗ f.hom := rfl

theorem negativeLiftedAction_map_left {X Y : C} (f : X ⟶ Y) (P : Mod_ M A) :
    letI := negativeLiftedAction C M A
    (f ⊵ₗ P).hom = f ⊵ₗ P.X := rfl

/-- The action still consists of actual additive functors on modules. -/
def negativeLiftedAction_left_additive (X : C) :
    letI := negativeLiftedAction C M A
    (MonoidalLeftAction.actionLeft (Mod_ M A) X).Additive := by
  letI := negativeLiftedAction C M A
  exact
    { map_add := by
        intro P Q f g
        apply Mod_.Hom.ext
        exact (MonoidalLeftAction.actionLeft M X).map_add }

def negativeLiftedAction_left_linear (X : C) :
    letI := negativeLiftedAction C M A
    (MonoidalLeftAction.actionLeft (Mod_ M A) X).Linear ℂ := by
  letI := negativeLiftedAction C M A
  exact
    { map_smul := by
        intro P Q f z
        apply Mod_.Hom.ext
        exact (MonoidalLeftAction.actionLeft M X).map_smul z f.hom }

section NativeProduct
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  (R B : Mon D)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual remaining right ambient action, presented as a genuine
left action of the monoidal opposite, on the actual product model. -/
def residualLeftAction : MonoidalLeftAction Dᴹᵒᵖ (Model R B) := by
  letI := (oppositeAlgebra B).mon
  exact negativeLiftedAction Dᴹᵒᵖ (Mod_ D R.X) (mop (oppositeAlgebra B).X)

/-- The same constructed action in native right-action notation. -/
def residualRightAction : MonoidalRightAction D (Model R B) := by
  letI := residualLeftAction R B
  exact MonoidalRightAction.rightActionOfMonoidalOppositeLeftAction D (Model R B)

theorem residualLeftAction_obj (X : Dᴹᵒᵖ) (P : Model R B) :
    letI := residualLeftAction R B
    (X ⊙ₗ P).X.X = P.X.X ⊗ X.unmop := rfl

theorem residualRightAction_obj (P : Model R B) (X : D) :
    letI := residualRightAction R B
    (P ⊙ᵣ X).X.X = P.X.X ⊗ X := rfl

theorem residualLeftAction_map_right (X : Dᴹᵒᵖ) {P Q : Model R B} (f : P ⟶ Q) :
    letI := residualLeftAction R B
    (X ⊴ₗ f).hom.hom = f.hom.hom ▷ X.unmop := rfl

theorem residualLeftAction_map_left {X Y : Dᴹᵒᵖ} (f : X ⟶ Y) (P : Model R B) :
    letI := residualLeftAction R B
    (f ⊵ₗ P).hom.hom = P.X.X ◁ f.unmop := rfl

def residualLeftAction_left_additive (X : Dᴹᵒᵖ) :
    letI := residualLeftAction R B
    (MonoidalLeftAction.actionLeft (Model R B) X).Additive := by
  letI := (oppositeAlgebra B).mon
  exact negativeLiftedAction_left_additive Dᴹᵒᵖ (Mod_ D R.X)
    (mop (oppositeAlgebra B).X) X

def residualLeftAction_left_linear (X : Dᴹᵒᵖ) :
    letI := residualLeftAction R B
    (MonoidalLeftAction.actionLeft (Model R B) X).Linear ℂ := by
  letI := (oppositeAlgebra B).mon
  exact negativeLiftedAction_left_linear Dᴹᵒᵖ (Mod_ D R.X)
    (mop (oppositeAlgebra B).X) X

def residualLeftAction_right_additive (P : Model R B) :
    letI := residualLeftAction R B
    (MonoidalLeftAction.actionRight Dᴹᵒᵖ P).Additive := by
  letI := residualLeftAction R B
  exact
    { map_add := by
        intro X Y f g
        apply Mod_.Hom.ext
        apply Mod_.Hom.ext
        exact (tensorLeft P.X.X).map_add }

def residualLeftAction_right_linear (P : Model R B) :
    letI := residualLeftAction R B
    (MonoidalLeftAction.actionRight Dᴹᵒᵖ P).Linear ℂ := by
  letI := residualLeftAction R B
  exact
    { map_smul := by
        intro X Y f z
        apply Mod_.Hom.ext
        apply Mod_.Hom.ext
        exact (tensorLeft P.X.X).map_smul z f.unmop }

/-- In particular the right algebra really crosses the new ambient
factor before its original action. The original two-sided action is not
incorrectly reused on the tensor product. -/
theorem residualLeftAction_right_action (X : Dᴹᵒᵖ) (P : Model R B) :
    letI := (oppositeAlgebra B).mon
    letI := residualLeftAction R B
    (γ[mop (oppositeAlgebra B).X,(X ⊙ₗ P).X]).hom =
      (α_ P.X.X X.unmop (oppositeAlgebra B).X).hom ≫
        P.X.X ◁ (β_ X.unmop (oppositeAlgebra B).X).hom ≫
          (α_ P.X.X (oppositeAlgebra B).X X.unmop).inv ≫
            (γ[mop (oppositeAlgebra B).X,P.X]).hom ▷ X.unmop := by
  letI := (oppositeAlgebra B).mon
  letI := residualLeftAction R B
  change ((Functor.LaxLeftLinear.μₗ
    ((ModuleAlphaInduction.negative Dᴹᵒᵖ (Mod_ D R.X)).obj X).toFunctor
      (mop (oppositeAlgebra B).X) P.X) ≫
        ((ModuleAlphaInduction.negative Dᴹᵒᵖ (Mod_ D R.X)).obj X).toFunctor.map
          γ[mop (oppositeAlgebra B).X,P.X]).hom = _
  rw [ModuleAlphaInduction.negative_μ]
  change ((α_ P.X.X X.unmop (oppositeAlgebra B).X).hom ≫
    P.X.X ◁ (β_ X.unmop (oppositeAlgebra B).X).hom ≫
      (α_ P.X.X (oppositeAlgebra B).X X.unmop).inv) ≫
        (γ[mop (oppositeAlgebra B).X,P.X]).hom ▷ X.unmop = _
  simp only [Category.assoc]

end NativeProduct
end Paper18.Category.GraphPicard.MoritaProduct
