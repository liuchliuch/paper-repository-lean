import Paper18.Category.ModuleFunctorFiniteInternalHomRightModules
import Paper18.Category.ModuleFunctorFiniteInternalHomMonadic

/-! # Actual internal algebra presentations of actual action components -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped MonoidalLeftAction
universe v u uM w wM
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

/-- Each actual action component is equivalent to native right modules
over its constructed internal endomorphism algebra. Actual simple
generation, monadicity, multiplication and orientation are all derived. -/
def componentRightModuleEquivalence (i : κ) :
    letI := endMonoid S (ModuleComponent.base (C := C) SM i)
    ModuleComponent.Component (C := C) SM i ≌
      Mod_ Cᴹᵒᵖ (mop (endObject S (ModuleComponent.base (C := C) SM i))) := by
  let n := ModuleComponent.base (C := C) SM i
  letI := endMonoid S n
  exact (componentMonadicEquivalence S SM i).trans
    ((Monad.algebraEquivOfIsoMonads (monadTensorIso S n)).trans
      (rightMonadModuleEquivalence (endObject S n)))

end Paper18.Category.ModuleInternalHom
