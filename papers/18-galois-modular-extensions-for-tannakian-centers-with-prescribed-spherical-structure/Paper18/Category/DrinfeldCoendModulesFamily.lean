import Paper18.Category.DrinfeldCoendModulesActionComponent

/-! # Arbitrary natural annular families and their actual rigid caps

This form is shared by the center-to-module construction and its inverse.
The naturality law is an actual equation on arbitrary morphisms of labels.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
universe v u
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D]

/-- The actual rigid cap associated to an arbitrary annular operator. -/
def capOf (T M : D) (h : T ⊗ M ⟶ T ⊗ M) : (dual D T ⊗ T) ⊗ M ⟶ M :=
  (α_ (dual D T) T M).hom ≫
    (tensorLeftHomEquiv (T ⊗ M) T (dual D T) M).symm h

lemma capOf_def (T M : D) (h : T ⊗ M ⟶ T ⊗ M) :
    capOf T M h = (α_ (dual D T) T M).hom ≫ dual D T ◁ h ≫
      (α_ (dual D T) T M).inv ≫ ε_ T (dual D T) ▷ M ≫ (λ_ M).hom := rfl

lemma capOf_transpose (T M : D) (h : T ⊗ M ⟶ T ⊗ M) :
    tensorLeftHomEquiv (T ⊗ M) T (dual D T) M
      ((α_ (dual D T) T M).inv ≫ capOf T M h) = h := by
  dsimp only [capOf]
  rw [Iso.inv_hom_id_assoc, Equiv.apply_symm_apply]

lemma capOf_injective (T M : D) : Function.Injective (capOf T M) := by
  intro h k he
  have hh := congrArg (fun q => tensorLeftHomEquiv (T ⊗ M) T (dual D T) M
    ((α_ (dual D T) T M).inv ≫ q)) he
  simpa only [capOf_transpose] using hh

lemma actionComponent_eq_capOf (Z : Center D) (T : D) :
    actionComponent Z T = capOf T Z.1 (holonomy Z T).hom := rfl

/-- Arbitrary actual natural annular families have actual dinatural cap families. -/
lemma capOf_dinaturality (M : D) (h : ∀ T : D, T ⊗ M ⟶ T ⊗ M)
    (hn : ∀ {T U : D} (f : T ⟶ U), f ▷ M ≫ h U = h T ≫ f ▷ M)
    {T U : D} (f : T ⟶ U) :
    (dualMap D f ▷ T) ▷ M ≫ capOf T M (h T) =
      (dual D U ◁ f) ▷ M ≫ capOf U M (h U) := by
  calc
    _ = (α_ (dual D U) T M).hom ≫ dual D U ◁ h T ≫
        (α_ (dual D U) T M).inv ≫
          ((dualMap D f ▷ T) ≫ ε_ T (dual D T)) ▷ M ≫ (λ_ M).hom := by
      rw [capOf_def]
      rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
        associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]
    _ = (α_ (dual D U) T M).hom ≫ dual D U ◁ h T ≫
        (α_ (dual D U) T M).inv ≫
          ((dual D U ◁ f) ≫ ε_ U (dual D U)) ▷ M ≫ (λ_ M).hom := by
      rw [rightAdjointMate_comp_evaluation]
    _ = (α_ (dual D U) T M).hom ≫ dual D U ◁ (h T ≫ f ▷ M) ≫
        (α_ (dual D U) U M).inv ≫ ε_ U (dual D U) ▷ M ≫ (λ_ M).hom := by monoidal
    _ = (α_ (dual D U) T M).hom ≫ dual D U ◁ (f ▷ M ≫ h U) ≫
        (α_ (dual D U) U M).inv ≫ ε_ U (dual D U) ▷ M ≫ (λ_ M).hom := by rw [hn]
    _ = _ := by rw [capOf_def]; monoidal

/-- The specified chosen-dual comparison changes the tensor cap exactly,
with no pivotal structure and no assumed tensor law for the operator. -/
lemma capOf_tensorDual (X Y M : D) (h : (X ⊗ Y) ⊗ M ⟶ (X ⊗ Y) ⊗ M) :
    ((dualTensorIso X Y).inv ▷ (X ⊗ Y)) ▷ M ≫ capOf (X ⊗ Y) M h =
      (α_ (dual D Y ⊗ dual D X) (X ⊗ Y) M).hom ≫
        (dual D Y ⊗ dual D X) ◁ h ≫
          (α_ (dual D Y ⊗ dual D X) (X ⊗ Y) M).inv ≫
            tensorEvaluation D X Y ▷ M ≫ (λ_ M).hom := by
  rw [capOf_def]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc,
    dualTensorIso_inv_evaluation]

end Paper18.Category.DrinfeldCoendModules
