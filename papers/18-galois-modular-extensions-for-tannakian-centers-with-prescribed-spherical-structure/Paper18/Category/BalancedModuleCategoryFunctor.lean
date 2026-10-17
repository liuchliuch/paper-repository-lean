import Paper18.Category.BalancedModuleCategoryBasic
import Mathlib.CategoryTheory.Products.Basic

/-! # The actual external bimodule bifunctor -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- Tensoring a genuine right module on its left uses the actual ambient
right action in the monoidal opposite. -/
abbrev rightAmbientTensor (N : RightModules B) (X : D) : RightModules B :=
  RelativeTensor.ambientTensor N (mop X)

def externalLeftMap {M M' : Mod_ D A} {N N' : RightModules B}
    (f : M ⟶ M') (g : N ⟶ N') :
    RelativeTensor.ambientTensor M (rightUnderlying N) ⟶
      RelativeTensor.ambientTensor M' (rightUnderlying N') :=
  RelativeTensor.ambientTensorMap f (rightUnderlying N) ≫
    RelativeTensor.ambientTensorMapRight M' g.hom.unmop

lemma externalLeftMap_hom {M M' : Mod_ D A} {N N' : RightModules B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (externalLeftMap f g).hom = f.hom ⊗ₘ g.hom.unmop :=
  (tensorHom_def f.hom g.hom.unmop).symm

def externalRightMap {M M' : Mod_ D A} {N N' : RightModules B}
    (f : M ⟶ M') (g : N ⟶ N') :
    rightAmbientTensor N M.X ⟶ rightAmbientTensor N' M'.X :=
  RelativeTensor.ambientTensorMap g (mop M.X) ≫
    RelativeTensor.ambientTensorMapRight N' f.hom.mop

lemma externalRightMap_hom {M M' : Mod_ D A} {N N' : RightModules B}
    (f : M ⟶ M') (g : N ⟶ N') :
    (externalRightMap f g).hom.unmop = f.hom ⊗ₘ g.hom.unmop :=
  (tensorHom_def' f.hom g.hom.unmop).symm

/-- The tensor of the two genuine module maps intertwines both actions. -/
def externalBimodMap {M M' : Mod_ D A} {N N' : RightModules B}
    (f : M ⟶ M') (g : N ⟶ N') : externalBimodObj M N ⟶ externalBimodObj M' N' where
  hom := f.hom ⊗ₘ g.hom.unmop
  left_act_hom := by
    have h := (externalLeftMap f g).isMod_Hom.smul_hom
    rw [externalLeftMap_hom] at h
    exact h
  right_act_hom := by
    have h := congrArg Quiver.Hom.unmop (externalRightMap f g).isMod_Hom.smul_hom
    simp only [unmop_comp] at h
    change ((α_ M.X (rightUnderlying N) B).hom ≫ M.X ◁ rightAction N) ≫
        (externalRightMap f g).hom.unmop =
      (externalRightMap f g).hom.unmop ▷ B ≫
        (α_ M'.X (rightUnderlying N') B).hom ≫ M'.X ◁ rightAction N' at h
    rw [externalRightMap_hom] at h
    simpa only [externalBimodObj, assoc] using h

/-- The genuine bifunctor into actual two-sided bimodule objects. -/
def externalBimod : Mod_ D A × RightModules B ⥤ Bimod (Mon.mk A) (Mon.mk B) where
  obj X := externalBimodObj X.1 X.2
  map f := externalBimodMap f.1 f.2
  map_id X := by
    apply Bimod.hom_ext
    exact id_tensorHom_id X.1.X (rightUnderlying X.2)
  map_comp f g := by
    apply Bimod.hom_ext
    exact (tensorHom_comp_tensorHom f.1.hom f.2.hom.unmop g.1.hom g.2.hom.unmop).symm

/-- The external tensor into the actual native iterated-module category. -/
def external : Mod_ D A × RightModules B ⥤ BimoduleRelativeTensor.Native A B :=
  externalBimod ⋙ BimoduleRelativeTensor.fromBimod A B

end Paper18.Category.BalancedModuleCategory
