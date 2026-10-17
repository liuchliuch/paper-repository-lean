import Paper18.Category.BalancedModuleCategoryGenerators

/-! # External pairs split through external free pairs using balancing

These retractions use only genuine input-module maps and the balancing
isomorphism, unlike a chosen presentation of an abstract native object.
They will therefore be preserved by every actual balanced functor.
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

/-- The right module's separability section gives an actual retract of
the ambient left tensor of its regular right module. -/
def rightFreeRetract (SB : SeparableAlgebra B) (N : RightModules B) :
    Retract N (rightAmbientTensor (Mod_.regular (mop B)) (rightUnderlying N)) :=
  leftFreeRetract (ModuleFunctor.separableMop SB) N

/-- A genuine external pair has a free presentation whose maps are
composites of actual external maps and a single balancing comparison. -/
def pairGeneratorRetract (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
    (M : Mod_ D A) (N : RightModules B) :
    Retract (externalObj M N)
      (externalObj (InternalModule.free A (M.X ⊗ rightUnderlying N)) (Mod_.regular (mop B))) :=
  ((rightFreeRetract SB N).map (CategoryTheory.Prod.sectR M _ ⋙ external)).trans
    ((Retract.ofIso (balancingIso M (rightUnderlying N) (Mod_.regular (mop B))).symm).trans
      ((leftFreeRetract SA (RelativeTensor.ambientTensor M (rightUnderlying N))).map
        (CategoryTheory.Prod.sectL _ (Mod_.regular (mop B)) ⋙ external)))

lemma pairGeneratorRetract_i (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
    (M : Mod_ D A) (N : RightModules B) :
    (pairGeneratorRetract SA SB M N).i =
      external.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightFreeRetract SB N).i) ≫
        (balancingIso M (rightUnderlying N) (Mod_.regular (mop B))).inv ≫
          external.map (CategoryTheory.Prod.mkHom
            (leftFreeRetract SA (RelativeTensor.ambientTensor M (rightUnderlying N))).i
              (𝟙 (Mod_.regular (mop B)))) := rfl

lemma pairGeneratorRetract_r (SA : SeparableAlgebra A) (SB : SeparableAlgebra B)
    (M : Mod_ D A) (N : RightModules B) :
    (pairGeneratorRetract SA SB M N).r =
      (external.map (CategoryTheory.Prod.mkHom
        (leftFreeRetract SA (RelativeTensor.ambientTensor M (rightUnderlying N))).r
          (𝟙 (Mod_.regular (mop B)))) ≫
            (balancingIso M (rightUnderlying N) (Mod_.regular (mop B))).hom) ≫
              external.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightFreeRetract SB N).r) := rfl

end Paper18.Category.BalancedModuleCategory
