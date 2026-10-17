import Paper18.Category.BimoduleRelativeTensorEquivalence
import Paper18.Category.RelativeTensorAmbient

/-! # The actual external tensor of a left and a right internal module

The first module category has the right ambient action M ↦ M ⊗ X.
The second consists of actual right modules, expressed as left modules in
the monoidal opposite. Their external tensor is an actual native bimodule.
No braiding or module-category universal property is assumed.
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

/-- Actual right B-modules, with all right-action laws supplied by native
internal modules in the reversed monoidal category. -/
abbrev RightModules (B : D) [MonObj B] := Mod_ Dᴹᵒᵖ (mop B)

abbrev rightUnderlying (N : RightModules B) : D := unmop N.X

abbrev rightAction (N : RightModules B) : rightUnderlying N ⊗ B ⟶ rightUnderlying N :=
  (γ[mop B,N.X]).unmop

@[reassoc]
lemma rightAction_one (N : RightModules B) :
    rightUnderlying N ◁ η[B] ≫ rightAction N = (ρ_ (rightUnderlying N)).hom :=
  congrArg Quiver.Hom.unmop (ModObj.one_smul (M := mop B) N.X)

@[reassoc]
lemma rightAction_assoc (N : RightModules B) :
    rightUnderlying N ◁ μ[B] ≫ rightAction N =
      (α_ (rightUnderlying N) B B).inv ≫ rightAction N ▷ B ≫ rightAction N :=
  congrArg Quiver.Hom.unmop (ModObj.mul_smul (M := mop B) N.X)

/-- The genuine two commuting actions on M ⊗ N. -/
def externalBimodObj (M : Mod_ D A) (N : RightModules B) : Bimod (Mon.mk A) (Mon.mk B) where
  X := M.X ⊗ rightUnderlying N
  actLeft := γ[A,(RelativeTensor.ambientTensor M (rightUnderlying N)).X]
  one_actLeft := ModObj.one_smul (M := A) (RelativeTensor.ambientTensor M (rightUnderlying N)).X
  left_assoc := ModObj.mul_smul (M := A) (RelativeTensor.ambientTensor M (rightUnderlying N)).X
  actRight := (α_ M.X (rightUnderlying N) B).hom ≫ M.X ◁ rightAction N
  actRight_one := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, rightAction_one]
    monoidal
  right_assoc := by
    rw [associator_naturality_right_assoc, ← whiskerLeft_comp, rightAction_assoc]
    simp only [whiskerLeft_comp, comp_whiskerRight, assoc]
    monoidal
  middle_assoc := by
    change ((α_ A M.X (rightUnderlying N)).inv ≫ γ[A,M.X] ▷ rightUnderlying N) ▷ B ≫
        (α_ M.X (rightUnderlying N) B).hom ≫ M.X ◁ rightAction N =
      (α_ A (M.X ⊗ rightUnderlying N) B).hom ≫
        A ◁ ((α_ M.X (rightUnderlying N) B).hom ≫ M.X ◁ rightAction N) ≫
          (α_ A M.X (rightUnderlying N)).inv ≫ γ[A,M.X] ▷ rightUnderlying N
    simp only [comp_whiskerRight, whiskerLeft_comp, assoc]
    rw [associator_naturality_left_assoc, ← whisker_exchange,
      associator_inv_naturality_right_assoc]
    monoidal

/-- The external tensor is an actual iterated native module, rather than
a pair of underlying objects with unproved compatibility. -/
def externalObj (M : Mod_ D A) (N : RightModules B) : BimoduleRelativeTensor.Native A B :=
  BimoduleRelativeTensor.fromBimodObj A B (externalBimodObj M N)

end Paper18.Category.BalancedModuleCategory
