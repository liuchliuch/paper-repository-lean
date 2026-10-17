import Paper18.Category.CentralFunctorAdjointSeparableNativeUnit
import Paper18.Category.CentralFunctorAdjointSeparableNativeMultiplication
import Mathlib.CategoryTheory.Monoidal.Mod_

/-! # Genuine diagonal modules of strong module functors

The actual native cap map satisfies both actual module laws. Its genuine
module morphisms are exactly the original native module transformations.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction MonObj
universe v u vM uM vN uN w wM
namespace Paper18.Category.CentralFunctorAdjointSeparable
open MonoidalLeftAction ModuleFunctor.DiagonalAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasFiniteBiproducts M] [MonoidalLeftAction C M]
  {κ : Type wM} [Fintype κ] (T : FiniteSemisimpleSkeleton M κ)
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteBiproducts N] [MonoidalLeftAction C N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X : C, (actionLeft M X).Additive] [∀ X : C, (actionLeft M X).Linear ℂ]
  [∀ X : C, (actionLeft N X).Additive] [∀ X : C, (actionLeft N X).Linear ℂ]
  [∀ m : M, (actionRight C m).Additive] [∀ m : M, (actionRight C m).Linear ℂ]
  [∀ n : N, (actionRight C n).Additive] [∀ n : N, (actionRight C n).Linear ℂ]

/-- The actual diagonal module of an actual strong module functor. -/
def diagonalModule (F : Ordinary C M N) :
    Mod_ (Ordinary C M N) (DiagonalAlgebra.canonicalAlgebra S) := by
  letI : ModObj (DiagonalAlgebra.canonicalAlgebra S) F :=
    { smul := nativeActionMap S T F
      one_smul' := nativeActionMap_one S T F
      mul_smul' := nativeActionMap_mul S T F }
  exact ⟨F⟩

/-- The construction keeps the actual original module-functor object. -/
@[simp]
lemma diagonalModule_X (F : Ordinary C M N) : (diagonalModule S T F).X = F := rfl

/-- An actual original module-natural transformation is an actual
morphism of the constructed diagonal modules. -/
def diagonalModuleHom {F G : Ordinary C M N} (τ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural C τ] : diagonalModule S T F ⟶ diagonalModule S T G :=
  Mod_.Hom.mk' τ (nativeActionMap_naturality S T τ)

@[simp]
lemma diagonalModuleHom_hom {F G : Ordinary C M N} (τ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural C τ] : (diagonalModuleHom S T τ).hom = τ := rfl

/-- The proved cap detection recovers actual original module naturality
from any genuine diagonal-module morphism. -/
theorem diagonalModuleHom_moduleNatural {F G : Ordinary C M N}
    (f : diagonalModule S T F ⟶ diagonalModule S T G) :
    ModuleFunctor.IsModuleNatural C f.hom :=
  (nativeActionMap_comm_iff S T f.hom).mp (IsMod_Hom.smul_hom (f := f.hom))

end Paper18.Category.CentralFunctorAdjointSeparable
