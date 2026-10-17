import Paper18.Category.BalancedModuleCategoryGenerators
import Paper18.Category.BimoduleRelativeTensorFreeHom

/-! # Native free maps factor through external maps and balancing

The formula below uses only maps from the two input module categories and
the actual balancing associator. It recovers every native map from a free
bimodule by the two proved free-module universal properties.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Native extension of an ambient coordinate by the actual two free
module lifts. -/
def coordinateLift {X : D} {P : BimoduleRelativeTensor.Native A B}
    (f : X ⟶ P.X.X) : doubleFree (A := A) (B := B) X ⟶ P :=
  ModuleFunctor.SeparableAction.freeLift (InternalModule.freeLift f)

lemma coordinateLift_hom {X : D} {P : BimoduleRelativeTensor.Native A B}
    (f : X ⟶ P.X.X) :
    (coordinateLift f).hom.hom =
      ((A ◁ f) ≫ γ[A,P.X.X]) ▷ B ≫ γ[mop B,P.X].hom := by
  have h := congrArg Mod_.Hom.hom
    (ModuleFunctor.SeparableAction.freeLift_hom (InternalModule.freeLift f))
  exact h

/-- Multiplication of the right regular module, as a genuine right module
map from its ambient left tensor with B. -/
def rightRegularMultiply :
    rightAmbientTensor (Mod_.regular (mop B)) B ⟶ Mod_.regular (mop B) :=
  InternalModule.actionHom (Mod_.regular (mop B))

@[simp] lemma doubleFreeExternalIso_inv_hom (X : D) :
    (doubleFreeExternalIso (A := A) (B := B) X).inv.hom.hom = 𝟙 ((A ⊗ X) ⊗ B) :=
  id_comp _

/-- The explicit external/balancing recipe for a free native map. -/
def externalFreeMap {X Y : D} (f : X ⟶ (A ⊗ Y) ⊗ B) :
    externalObj (InternalModule.free A X) (Mod_.regular (mop B)) ⟶
      externalObj (InternalModule.free A Y) (Mod_.regular (mop B)) :=
  external.map (CategoryTheory.Prod.mkHom (InternalModule.freeMap f) (𝟙 _)) ≫
    external.map (CategoryTheory.Prod.mkHom (RelativeTensor.ambientFreeIso (A ⊗ Y) B).inv (𝟙 _)) ≫
      (balancingIso (InternalModule.free A (A ⊗ Y)) B (Mod_.regular (mop B))).hom ≫
        external.map (CategoryTheory.Prod.mkHom (InternalModule.actionHom (InternalModule.free A Y))
          (rightRegularMultiply (B := B)))

/-- The recipe is the genuine native free lift, proved by actual
associator naturality. No prescribed formula for free maps is assumed. -/
theorem externalFreeMap_eq_coordinateLift {X Y : D} (f : X ⟶ (A ⊗ Y) ⊗ B) :
    externalFreeMap f = (doubleFreeExternalIso X).inv ≫
      coordinateLift (P := externalObj (InternalModule.free A Y) (Mod_.regular (mop B))) f := by
  apply Mod_.Hom.ext
  apply Mod_.Hom.ext
  simp only [Mod_.comp_hom', doubleFreeExternalIso_inv_hom]
  rw [coordinateLift_hom]
  change ((A ◁ f) ⊗ₘ 𝟙 B) ≫ ((α_ A (A ⊗ Y) B).inv ⊗ₘ 𝟙 B) ≫
      (α_ (A ⊗ (A ⊗ Y)) B B).hom ≫
        (γ[A,(InternalModule.free A Y).X] ⊗ₘ μ[B]) =
    𝟙 ((A ⊗ X) ⊗ B) ≫
      ((A ◁ f) ≫ (α_ A (A ⊗ Y) B).inv ≫ γ[A,(InternalModule.free A Y).X] ▷ B) ▷ B ≫
        (α_ (A ⊗ Y) B B).hom ≫ (A ⊗ Y) ◁ μ[B]
  rw [id_comp]
  simp only [MonoidalCategory.tensorHom_def, comp_whiskerRight, whiskerLeft_id, id_comp, assoc]
  have hn : γ[A,(InternalModule.free A Y).X] ▷ B ▷ B ≫ (α_ (A ⊗ Y) B B).hom =
      (α_ (A ⊗ (A ⊗ Y)) B B).hom ≫ γ[A,(InternalModule.free A Y).X] ▷ (B ⊗ B) :=
    MonoidalCategory.associator_naturality_left γ[A,(InternalModule.free A Y).X] B B
  rw [reassoc_of% hn]
  rfl

section Linear
variable [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]

lemma coordinateLift_eq_linearEquiv {X : D} {P : BimoduleRelativeTensor.Native A B}
    (f : X ⟶ P.X.X) :
    coordinateLift f = (BimoduleRelativeTensor.doubleFreeHomLinearEquiv A B X P).symm f := rfl

/-- Every genuine native map between external free generators has the
explicit external/balancing factorization. -/
theorem externalFreeMap_factorization {X Y : D}
    (g : externalObj (InternalModule.free A X) (Mod_.regular (mop B)) ⟶
      externalObj (InternalModule.free A Y) (Mod_.regular (mop B))) :
    g = externalFreeMap (A := A) (B := B) (X := X) (Y := Y)
      (BimoduleRelativeTensor.doubleFreeHomLinearEquiv A B X _
        ((doubleFreeExternalIso X).hom ≫ g)) := by
  rw [externalFreeMap_eq_coordinateLift, coordinateLift_eq_linearEquiv,
    LinearEquiv.symm_apply_apply]
  simp only [← assoc, Iso.inv_hom_id, id_comp]

end Linear
end Paper18.Category.BalancedModuleCategory
