import Paper18.Category.BimoduleRelativeTensorFunctorCompositionModule

/-! # Mixed-algebra coherence of actual relative tensor functors

These are genuine natural-component equations for arbitrary four algebra
objects. They retain the actual reversed functor-composition order and
follow from the native bimodule pentagon and triangle.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {R S T U : D} [MonObj R] [MonObj S] [MonObj T] [MonObj U]

/-- The actual comparison for three arbitrary composable bimodules
satisfies the actual composition pentagon at every module. -/
lemma tensorComposition_pentagon (P : Native R S) (Q : Native S T)
    (W : Native T U) (N : Mod_ D U) :
    (tensorCompositionIso (tensor P Q) W).hom.app N ≫
        (tensorCompositionIso P Q).hom.app ((tensorFunctor W).obj N) =
      (tensorNat (associator P Q W).hom).app N ≫
        (tensorCompositionIso P (tensor Q W)).hom.app N ≫
          (tensorFunctor P).map ((tensorCompositionIso Q W).hom.app N) := by
  apply Mod_.Hom.ext
  exact congrArg (fun k => k.hom.hom) (pentagon P Q W (moduleAsNative N)).symm

/-- Contracting the left regular bimodule agrees with the actual
identity-module-functor comparison. -/
lemma tensorComposition_left_unitality (P : Native R S) (N : Mod_ D S) :
    (tensorCompositionIso (regular R) P).hom.app N ≫
        (tensorUnitIso R).hom.app ((tensorFunctor P).obj N) =
      (tensorNat (leftUnitor P).hom).app N := by
  apply Mod_.Hom.ext
  letI := nativeBicategory (D := D)
  exact congrArg (fun k => k.hom.hom) (Bicategory.leftUnitor_whiskerRight
    (a := Mon.mk R) (b := Mon.mk S) (c := Mon.mk (𝟙_ D)) P (moduleAsNative N)).symm

/-- Contracting the right regular bimodule agrees with the actual
identity-module-functor comparison. -/
lemma tensorComposition_right_unitality (P : Native R S) (N : Mod_ D S) :
    (tensorCompositionIso P (regular S)).hom.app N ≫
        (tensorFunctor P).map ((tensorUnitIso S).hom.app N) =
      (tensorNat (rightUnitor P).hom).app N := by
  apply Mod_.Hom.ext
  exact congrArg (fun k => k.hom.hom) (triangle P (moduleAsNative N))

end Paper18.Category.BimoduleRelativeTensor
