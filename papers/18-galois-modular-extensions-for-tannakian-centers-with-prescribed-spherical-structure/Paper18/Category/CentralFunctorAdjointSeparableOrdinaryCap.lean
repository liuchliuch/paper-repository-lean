import Paper18.Category.CentralFunctorAdjointSeparableTensorCap
import Paper18.Category.ModuleFunctorDiagonalActionPair

/-! # Actual diagonal cap maps in the ordinary module-functor category -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [MonoidalLeftAction C N]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]

/-- The actual cap coordinate, as an actual ordinary transformation
between objects with their genuine retained module structures. -/
def ordinaryCap (F : Ordinary C M N) (X : C) : pairObject Xᘁ X F ⟶ F :=
  capComponent (toFunctor F) X Xᘁ

@[simp] lemma ordinaryCap_app (F : Ordinary C M N) (X : C) (m : M) :
    (ordinaryCap F X).app m = (capComponent (toFunctor F) X Xᘁ).app m := rfl

/-- The actual pair-action morphisms satisfy the true cap dinaturality. -/
lemma ordinaryCap_dinaturality (F : Ordinary C M N) {X Y : C} (f : X ⟶ Y) :
    (pairMapLeft (dualMap C f) X).app F ≫ ordinaryCap F X =
      (pairMapRight Yᘁ f).app F ≫ ordinaryCap F Y := by
  apply NatTrans.ext
  funext m
  change dualMap C f ⊵ₗ (toFunctor F).obj (X ⊙ₗ m) ≫
      (capComponent (toFunctor F) X Xᘁ).app m =
    Yᘁ ⊴ₗ (toFunctor F).map (f ⊵ₗ m) ≫
      (capComponent (toFunctor F) Y Yᘁ).app m
  exact capComponent_dinaturality (toFunctor F) f m

/-- Commutation with actual diagonal cap maps is exactly native module
naturality. This will reflect separable averaging back to genuine module
transformations. -/
theorem ordinaryCap_comm_iff {F G : Ordinary C M N} (τ : F ⟶ G) :
    (∀ X : C, ordinaryCap F X ≫ τ =
        (pairEnd (M := M) (N := N) Xᘁ X).map τ ≫ ordinaryCap G X) ↔
      ModuleFunctor.IsModuleNatural C τ := by
  rw [moduleNatural_iff_capComponent]
  constructor
  · intro h X m
    exact congrArg (fun k => k.app m) (h X)
  · intro h X
    apply NatTrans.ext
    funext m
    exact h X m

end Paper18.Category.CentralFunctorAdjointSeparable
