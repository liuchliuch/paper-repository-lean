import Paper18.Category.CentralFunctorAdjointSeparableCap

/-! # Dinaturality of the actual native cap coordinates -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u vM uM vN uN
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
attribute [local instance 2000] RightRigidCategory.rightDual
variable {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {N : Type uN} [Category.{vN} N] [MonoidalLeftAction C N]

/-- Actual native action evaluations inherit the actual rigid mate
dinaturality, including the action associators. -/
lemma actionEvaluation_dinaturality {X Y : C} (f : X ⟶ Y) (m : M) :
    dualMap C f ⊵ₗ (X ⊙ₗ m) ≫
        (ModuleFunctor.actionEvaluation M X Xᘁ).app m =
      Yᘁ ⊴ₗ (f ⊵ₗ m) ≫ (ModuleFunctor.actionEvaluation M Y Yᘁ).app m := by
  simp only [ModuleFunctor.actionEvaluation_app]
  calc
    _ = (αₗ Yᘁ X m).inv ≫
        ((dualMap C f ▷ X) ≫ ε_ X Xᘁ) ⊵ₗ m ≫ (λₗ[C] m).hom := by
      rw [comp_actionHomLeft]
      simp only [whiskerRight_actionHomLeft, Category.assoc, Iso.inv_hom_id_assoc]
    _ = (αₗ Yᘁ X m).inv ≫
        ((Yᘁ ◁ f) ≫ ε_ Y Yᘁ) ⊵ₗ m ≫ (λₗ[C] m).hom := by
      rw [rightAdjointMate_comp_evaluation]
    _ = _ := by
      rw [comp_actionHomLeft]
      simp only [whiskerLeft_actionHomLeft, Category.assoc, Iso.inv_hom_id_assoc]

variable (F : M ⥤ N) [F.LeftLinear C]

/-- Sliding an actual source morphism across a cap takes precisely its
actual right dual mate. -/
lemma capComponent_dinaturality {X Y : C} (f : X ⟶ Y) (m : M) :
    dualMap C f ⊵ₗ F.obj (X ⊙ₗ m) ≫ (capComponent F X Xᘁ).app m =
      Yᘁ ⊴ₗ F.map (f ⊵ₗ m) ≫ (capComponent F Y Yᘁ).app m := by
  simp only [capComponent_app]
  rw [← Category.assoc, Functor.LaxLeftLinear.μₗ_naturality_left,
    Category.assoc, ← F.map_comp, actionEvaluation_dinaturality]
  rw [F.map_comp, ← Category.assoc]
  erw [← Functor.LaxLeftLinear.μₗ_naturality_right F Yᘁ (f ⊵ₗ m)]
  rw [Category.assoc]

end Paper18.Category.CentralFunctorAdjointSeparable
