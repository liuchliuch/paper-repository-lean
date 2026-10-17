import Paper18.Category.ModuleFunctorFiniteInternalHomFaithful
import Paper18.Category.FixedBoundarySemisimpleExact
import Paper18.Category.SemisimpleAbelian
import Mathlib.CategoryTheory.Monad.Monadicity
import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced

/-! # Actual monadic presentation of an actual simple action component -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w wM
namespace Paper18.Category.ModuleInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{v} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Additive]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Linear ℂ]
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)

/-- The actual internal-Hom functor is monadic when actual simple action
retracts generate the specified category. Exactness is derived from
actual semisimple cokernel splittings. -/
def monadicOfSimpleRetracts (n : M)
    (hgen : ∀ j : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject j) (X ⊙ₗ n))) :
    MonadicRightAdjoint (internalHomFunctor S n).toFunctor := by
  letI := faithfulOfSimpleRetracts S SM n hgen
  letI : Abelian M := SM.abelian
  letI : HasCoequalizers M := SM.hasCoequalizers
  letI : PreservesColimitsOfShape WalkingParallelPair (internalHomFunctor S n).toFunctor :=
    SM.preservesCoequalizers (internalHomFunctor S n).toFunctor
  letI : Monad.PreservesColimitOfIsReflexivePair (internalHomFunctor S n).toFunctor :=
    { out := fun {X Y} f g _ =>
      inferInstanceAs (PreservesColimit (parallelPair f g) (internalHomFunctor S n).toFunctor) }
  exact Monad.monadicOfHasPreservesReflexiveCoequalizersOfReflectsIsomorphisms (adjunction S n)

/-- The actual comparison to the genuine adjunction-monad algebras is an
actual equivalence, with no monadicity conclusion assumed. -/
def equivalenceOfSimpleRetracts (n : M)
    (hgen : ∀ j : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject j) (X ⊙ₗ n))) :
    M ≌ Monad.Algebra (adjunction S n).toMonad := by
  letI h := monadicOfSimpleRetracts S SM n hgen
  letI : (Monad.comparison (adjunction S n)).IsEquivalence :=
    show (Monad.comparison (monadicAdjunction (internalHomFunctor S n).toFunctor)).IsEquivalence from
      inferInstance
  exact (Monad.comparison (adjunction S n)).asEquivalence

/-- Each genuine simple action component has an actual internal-Hom
monadic presentation. The required simple generation is proved from the
actual action by the component construction. -/
def componentMonadicEquivalence (i : κ) :
    ModuleComponent.Component (C := C) SM i ≌
      Monad.Algebra (adjunction S (ModuleComponent.base (C := C) SM i)).toMonad := by
  letI : HasKernels (ModuleComponent.Component (C := C) SM i) := ModuleComponent.hasKernels SM i
  exact equivalenceOfSimpleRetracts S (ModuleComponent.skeleton (C := C) SM i)
    (ModuleComponent.base (C := C) SM i) (ModuleComponent.simple_retract_action_base SM i)

end Paper18.Category.ModuleInternalHom
