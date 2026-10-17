import Paper18.Category.BimoduleRelativeTensorMoritaInverse
import Mathlib.CategoryTheory.Bicategory.Adjunction.Basic

/-! # Actual coherent Morita equivalences in the native bimodule bicategory -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u
namespace Paper18.Category.BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  {R S : D} [MonObj R] [MonObj S]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable (P : Native R S) [(tensorFunctor P).IsEquivalence]

/-- Actual inverse quotient functors produce an actual coherent native
Morita equivalence. The triangle equations are proved by bicategorical
adjointification of the two already constructed actual product isomorphisms. -/
def moritaEquivalenceOfTensorFunctor (SepR : SeparableAlgebra R) (SepS : SeparableAlgebra S) :
    letI := nativeBicategory (D := D)
    Bicategory.Equivalence (Mon.mk R) (Mon.mk S) := by
  letI := nativeBicategory (D := D)
  exact Bicategory.Equivalence.mkOfAdjointifyCounit
    (inverseBimoduleLeftIso P SepR).symm (inverseBimoduleRightIso P SepR SepS)

@[simp] lemma moritaEquivalenceOfTensorFunctor_hom
    (SepR : SeparableAlgebra R) (SepS : SeparableAlgebra S) :
    letI := nativeBicategory (D := D)
    (moritaEquivalenceOfTensorFunctor P SepR SepS).hom = P := rfl

@[simp] lemma moritaEquivalenceOfTensorFunctor_inv
    (SepR : SeparableAlgebra R) (SepS : SeparableAlgebra S) :
    letI := nativeBicategory (D := D)
    (moritaEquivalenceOfTensorFunctor P SepR SepS).inv = inverseBimodule P := rfl

end Paper18.Category.BimoduleRelativeTensor
