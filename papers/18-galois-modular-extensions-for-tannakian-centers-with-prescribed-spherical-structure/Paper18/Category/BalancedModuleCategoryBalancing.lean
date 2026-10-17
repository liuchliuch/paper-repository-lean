import Paper18.Category.BalancedModuleCategoryFunctor
import Mathlib.CategoryTheory.Products.Associator

/-! # The actual balancing associator and its coherence

The external tensor of a left and a right module is balanced over the
ambient monoidal category. The comparison and both of its coherence laws
are proved using actual native module maps and ambient monoidal coherence.
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

/-- Ambient tensoring on the right, as a genuine bifunctor. -/
def ambientRightFunctor : Mod_ D A × D ⥤ Mod_ D A where
  obj X := RelativeTensor.ambientTensor X.1 X.2
  map f := RelativeTensor.ambientTensorMap f.1 _ ≫ RelativeTensor.ambientTensorMapRight _ f.2
  map_id X := by
    apply Mod_.Hom.ext
    change (𝟙 X.1.X) ▷ X.2 ≫ X.1.X ◁ 𝟙 X.2 = 𝟙 _
    simp
  map_comp f g := by
    apply Mod_.Hom.ext
    change (f.1.hom ≫ g.1.hom) ▷ _ ≫ _ ◁ (f.2 ≫ g.2) =
      (f.1.hom ▷ _ ≫ _ ◁ f.2) ≫ (g.1.hom ▷ _ ≫ _ ◁ g.2)
    simp only [comp_whiskerRight, whiskerLeft_comp, assoc]
    rw [whisker_exchange_assoc]

lemma ambientRightFunctor_map_hom {X Y : Mod_ D A × D} (f : X ⟶ Y) :
    (ambientRightFunctor.map f).hom = f.1.hom ⊗ₘ f.2 :=
  (tensorHom_def f.1.hom f.2).symm

/-- Actual tensoring on the left of a genuine right module. -/
def ambientLeftFunctor : D × RightModules B ⥤ RightModules B :=
  (mopFunctor D).prod (𝟭 _) ⋙ CategoryTheory.Prod.swap _ _ ⋙ ambientRightFunctor

lemma ambientLeftFunctor_map_hom {X Y : D × RightModules B} (f : X ⟶ Y) :
    (ambientLeftFunctor.map f).hom.unmop = f.1 ⊗ₘ f.2.hom.unmop :=
  (tensorHom_def' f.1 f.2.hom.unmop).symm

/-- The ambient associator intertwines both genuine algebra actions. -/
def balancingBimodIso (M : Mod_ D A) (X : D) (N : RightModules B) :
    externalBimodObj (RelativeTensor.ambientTensor M X) N ≅
      externalBimodObj M (rightAmbientTensor N X) :=
  Bimod.isoOfIso (α_ M.X X (rightUnderlying N))
    (RelativeTensor.ambientTensorAssoc M X (rightUnderlying N)).hom.isMod_Hom.smul_hom
    (congrArg Quiver.Hom.unmop
      (RelativeTensor.ambientTensorAssoc N (mop X) (mop M.X)).inv.isMod_Hom.smul_hom)

/-- The actual balancing isomorphism in the native bimodule model. -/
def balancingIso (M : Mod_ D A) (X : D) (N : RightModules B) :
    externalObj (RelativeTensor.ambientTensor M X) N ≅
      externalObj M (rightAmbientTensor N X) :=
  (BimoduleRelativeTensor.fromBimod A B).mapIso (balancingBimodIso M X N)

/-- The genuine functor in which the ambient object acts on the first
module before the external tensor. -/
def balancedLeft : (Mod_ D A × D) × RightModules B ⥤ BimoduleRelativeTensor.Native A B :=
  ambientRightFunctor.prod (𝟭 _) ⋙ external

/-- The genuine functor in which the ambient object acts on the second
module before the external tensor. -/
def balancedRight : (Mod_ D A × D) × RightModules B ⥤ BimoduleRelativeTensor.Native A B :=
  CategoryTheory.prod.associator _ _ _ ⋙ (𝟭 _).prod ambientLeftFunctor ⋙ external

/-- The balancing comparison is an actual natural isomorphism in all
three variables, not just an objectwise family of ambient maps. -/
def balancing : balancedLeft (A := A) (B := B) ≅ balancedRight :=
  NatIso.ofComponents (fun X => balancingIso X.1.1 X.1.2 X.2) (by
    intro X Y f
    apply Mod_.Hom.ext
    apply Mod_.Hom.ext
    change ((ambientRightFunctor.map f.1).hom ⊗ₘ f.2.hom.unmop) ≫
        (α_ Y.1.1.X Y.1.2 (rightUnderlying Y.2)).hom =
      (α_ X.1.1.X X.1.2 (rightUnderlying X.2)).hom ≫
        (f.1.1.hom ⊗ₘ (ambientLeftFunctor.map (CategoryTheory.Prod.mkHom f.1.2 f.2)).hom.unmop)
    rw [ambientRightFunctor_map_hom, ambientLeftFunctor_map_hom]
    exact associator_naturality f.1.1.hom f.1.2 f.2.hom.unmop)

/-- The actual associator on the right-module ambient action, including
the reversal of the two ambient factors. -/
def rightAmbientAssoc (N : RightModules B) (X Y : D) :
    rightAmbientTensor (rightAmbientTensor N Y) X ≅ rightAmbientTensor N (X ⊗ Y) :=
  RelativeTensor.ambientTensorAssoc N (mop Y) (mop X)

theorem balancing_pentagon (M : Mod_ D A) (X Y : D) (N : RightModules B) :
    external.map (CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorAssoc M X Y).hom (𝟙 N)) ≫
        (balancingIso M (X ⊗ Y) N).hom =
      (balancingIso (RelativeTensor.ambientTensor M X) Y N).hom ≫
        (balancingIso M X (rightAmbientTensor N Y)).hom ≫
          external.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightAmbientAssoc N X Y).hom) := by
  apply Mod_.Hom.ext
  apply Mod_.Hom.ext
  change ((α_ M.X X Y).hom ⊗ₘ 𝟙 (rightUnderlying N)) ≫
      (α_ M.X (X ⊗ Y) (rightUnderlying N)).hom =
    (α_ (M.X ⊗ X) Y (rightUnderlying N)).hom ≫
      (α_ M.X X (Y ⊗ rightUnderlying N)).hom ≫
        (𝟙 M.X ⊗ₘ (α_ X Y (rightUnderlying N)).inv)
  monoidal

theorem balancing_unit (M : Mod_ D A) (N : RightModules B) :
    (balancingIso M (𝟙_ D) N).hom ≫
        external.map (CategoryTheory.Prod.mkHom (𝟙 M) (InternalModule.ambientTensorUnit N).hom) =
      external.map (CategoryTheory.Prod.mkHom (InternalModule.ambientTensorUnit M).hom (𝟙 N)) := by
  apply Mod_.Hom.ext
  apply Mod_.Hom.ext
  change (α_ M.X (𝟙_ D) (rightUnderlying N)).hom ≫
      (𝟙 M.X ⊗ₘ (λ_ (rightUnderlying N)).hom) = (ρ_ M.X).hom ⊗ₘ 𝟙 (rightUnderlying N)
  monoidal

end Paper18.Category.BalancedModuleCategory
