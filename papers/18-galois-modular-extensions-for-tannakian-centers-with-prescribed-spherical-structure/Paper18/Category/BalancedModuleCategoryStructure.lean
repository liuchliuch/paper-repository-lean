import Paper18.Category.BalancedModuleCategoryBalancing
import Mathlib.CategoryTheory.Whiskering

/-! # Actual balanced functors and the constructed native example

Balancing is an actual natural isomorphism with its defining action
coherence laws. There is no universal property or relative-product
equivalence field. The native example below satisfies these laws by the
previously proved associator computations.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u vE uE vE' uE'
namespace Paper18.Category.BalancedModuleCategory
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  {A B : D} [MonObj A] [MonObj B]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (E : Type uE) [Category.{vE} E]

def leftFor (F : Mod_ D A × RightModules B ⥤ E) :
    (Mod_ D A × D) × RightModules B ⥤ E := ambientRightFunctor.prod (𝟭 _) ⋙ F

def rightFor (F : Mod_ D A × RightModules B ⥤ E) :
    (Mod_ D A × D) × RightModules B ⥤ E :=
  CategoryTheory.prod.associator _ _ _ ⋙ (𝟭 _).prod ambientLeftFunctor ⋙ F

/-- Actual coherent balanced functor data. The coherence fields define
what it means to be balanced; none asserts a universal product property. -/
structure BalancedFunctor where
  toFunctor : Mod_ D A × RightModules B ⥤ E
  comparison : leftFor E toFunctor ≅ rightFor E toFunctor
  assoc_condition : ∀ (M : Mod_ D A) (X Y : D) (N : RightModules B),
    toFunctor.map (CategoryTheory.Prod.mkHom (RelativeTensor.ambientTensorAssoc M X Y).hom (𝟙 N)) ≫
        comparison.hom.app ((M, X ⊗ Y), N) =
      comparison.hom.app ((RelativeTensor.ambientTensor M X, Y), N) ≫
        comparison.hom.app ((M, X), rightAmbientTensor N Y) ≫
          toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (rightAmbientAssoc N X Y).hom)
  unit_condition : ∀ (M : Mod_ D A) (N : RightModules B),
    comparison.hom.app ((M, 𝟙_ D), N) ≫
        toFunctor.map (CategoryTheory.Prod.mkHom (𝟙 M) (InternalModule.ambientTensorUnit N).hom) =
      toFunctor.map (CategoryTheory.Prod.mkHom (InternalModule.ambientTensorUnit M).hom (𝟙 N))

/-- The previously constructed external tensor is an actual balanced
functor. Its defining coherence laws are proved, not additional inputs. -/
def nativeBalanced : BalancedFunctor (A := A) (B := B) (BimoduleRelativeTensor.Native A B) where
  toFunctor := external
  comparison := balancing
  assoc_condition := balancing_pentagon
  unit_condition := balancing_unit

namespace BalancedFunctor
variable {E} (F : BalancedFunctor (A := A) (B := B) E)
  {E' : Type uE'} [Category.{vE'} E']

/-- Every actual functor out of the native model gives an actual balanced
functor by postcomposition. This constructs the universal comparison map;
it does not assume that this comparison is an equivalence. -/
def postcompose (H : E ⥤ E') : BalancedFunctor (A := A) (B := B) E' where
  toFunctor := F.toFunctor ⋙ H
  comparison := Functor.isoWhiskerRight F.comparison H
  assoc_condition M X Y N := by
    simpa only [Functor.map_comp] using congrArg (fun f => H.map f) (F.assoc_condition M X Y N)
  unit_condition M N := by
    simpa only [Functor.map_comp] using congrArg (fun f => H.map f) (F.unit_condition M N)

end BalancedFunctor
end Paper18.Category.BalancedModuleCategory
