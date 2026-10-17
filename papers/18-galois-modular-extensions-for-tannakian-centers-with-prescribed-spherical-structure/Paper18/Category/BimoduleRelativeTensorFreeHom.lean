import Paper18.Category.BimoduleRelativeTensorBasic
import Paper18.Category.RelativeTensorAdjunction

/-! # Actual free bimodule Hom coordinates

The two native free-module universal properties give the actual linear
Hom equivalence from the free two-sided module. No separability,
commutativity, braiding or pivotal structure is needed.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vM uM
namespace Paper18.Category.BimoduleRelativeTensor.ExternalFree
open MonoidalLeftAction
open ModuleFunctor.SeparableAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type uM} [Category.{vM} M] [MonoidalLeftAction C M]
  {A : C} [MonObj A]

def unit (X : M) : X ⟶ (free (A := A) X).X :=
  (λₗ[C] X).inv ≫ η[A] ⊵ₗ X

lemma action_unit (X : M) :
    A ⊴ₗ unit (A := A) X ≫ γ[A,(free (A := A) X).X] = 𝟙 _ := by
  have ht : A ⊴ₗ (η[A] ⊵ₗ X) ≫ (αₗ A A X).inv =
      (αₗ A (𝟙_ C) X).inv ≫ (A ◁ η[A]) ⊵ₗ X := by
    rw [whiskerLeft_actionHomLeft]
    simp only [Iso.inv_hom_id_assoc]
  have hu : (A ⊴ₗ (λₗ[C] X).inv) ≫ (αₗ A (𝟙_ C) X).inv = (ρ_ A).inv ⊵ₗ X := by
    apply (cancel_mono ((ρ_ A).hom ⊵ₗ X)).mp
    calc
      _ = 𝟙 _ := by
        rw [rightUnitor_actionHom, assoc, Iso.inv_hom_id_assoc,
          ← actionHomRight_comp, Iso.inv_hom_id, actionHomRight_id]
      _ = _ := by rw [← comp_actionHomLeft, Iso.inv_hom_id, id_actionHomLeft]
  rw [unit, free_smul, actionHomRight_comp, assoc, reassoc_of% ht, reassoc_of% hu]
  rw [← comp_actionHomLeft, MonObj.mul_one, ← comp_actionHomLeft,
    Iso.inv_hom_id, id_actionHomLeft]

variable [Preadditive M] [Linear ℂ M]
  [∀ c : C, (actionLeft M c).Additive] [∀ c : C, (actionLeft M c).Linear ℂ]

/-- The actual complex-linear free-module universal property for an
arbitrary native action. -/
def homLinearEquiv (X : M) (Y : Mod_ M A) :
    (free (A := A) X ⟶ Y) ≃ₗ[ℂ] (X ⟶ Y.X) where
  toFun f := unit X ≫ f.hom
  invFun := freeLift
  left_inv f := by
    apply Mod_.Hom.ext
    change A ⊴ₗ (unit X ≫ f.hom) ≫ γ[A,Y.X] = f.hom
    have hf : γ[A,(free (A := A) X).X] ≫ f.hom = (A ⊴ₗ f.hom) ≫ γ[A,Y.X] :=
      f.isMod_Hom.smul_hom
    rw [actionHomRight_comp, assoc, ← hf, ← assoc, action_unit, id_comp]
  right_inv f := by simpa only [unit, assoc] using unit_freeLift f
  map_add' f g := by
    change unit X ≫ (f.hom + g.hom) = _
    rw [Preadditive.comp_add]
  map_smul' z f := by
    change unit X ≫ (z • f.hom) = _
    rw [Linear.comp_smul, RingHom.id_apply]

end Paper18.Category.BimoduleRelativeTensor.ExternalFree

namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (R S : D) [MonObj R] [MonObj S]

/-- The actual free left R, right S bimodule on an ambient object. -/
def doubleFree (X : D) : Native R S :=
  ModuleFunctor.SeparableAction.free (A := mop S) (InternalModule.free R X)

@[simp] lemma doubleFree_X (X : D) : (doubleFree R S X).X.X = (R ⊗ X) ⊗ S := rfl

/-- Actual maps from the actual free bimodule are exactly ambient maps
to the underlying object, including their complex-linear structures. -/
def doubleFreeHomLinearEquiv (X : D) (P : Native R S) :
    (doubleFree R S X ⟶ P) ≃ₗ[ℂ] (X ⟶ P.X.X) :=
  (ExternalFree.homLinearEquiv (A := mop S) (InternalModule.free R X) P).trans
    (RelativeTensor.freeHomLinearEquiv X P.X)

lemma finrank_doubleFree_hom (X : D) (P : Native R S) :
    Module.finrank ℂ (doubleFree R S X ⟶ P) = Module.finrank ℂ (X ⟶ P.X.X) :=
  (doubleFreeHomLinearEquiv R S X P).finrank_eq

end Paper18.Category.BimoduleRelativeTensor
