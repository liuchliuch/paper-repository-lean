import Paper18.Category.CentralFunctorAdjointSeparableNativeModules
import Paper18.Category.GraphLagrangianNoPivotal
import Paper18.Category.ModuleFunctorSemisimpleSeparableAction

/-! # Genuine averaging onto native module transformations

Actual separability of the canonical diagonal algebra averages arbitrary
ordinary transformations between actual strong module functors. Actual
cap detection proves that the resulting transformation is module natural.
No pivotal data or module-naturality conclusion is supplied as input.
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

/-- Actual separable averaging gives a genuine diagonal-module morphism. -/
def diagonalAverageHom {F G : Ordinary C M N} (τ : F ⟶ G) :
    diagonalModule S T F ⟶ diagonalModule S T G :=
  ModuleFunctor.SeparableAction.average
    (DiagonalAlgebra.canonicalSeparableNoPivotal S) τ

/-- The actual ordinary transformation obtained by separable averaging. -/
def averageNative {F G : Ordinary C M N} (τ : F ⟶ G) : F ⟶ G :=
  (diagonalAverageHom S T τ).hom

/-- Native module naturality is proved by the actual cap-coordinate
detection theorem, applied to the actual averaged diagonal-module map. -/
instance averageNative_moduleNatural {F G : Ordinary C M N} (τ : F ⟶ G) :
    ModuleFunctor.IsModuleNatural C (averageNative S T τ) :=
  diagonalModuleHom_moduleNatural S T (diagonalAverageHom S T τ)

/-- Averaging fixes every actual module-natural transformation. -/
@[simp]
lemma averageNative_moduleHom {F G : Ordinary C M N} (τ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural C τ] : averageNative S T τ = τ := by
  exact congrArg Mod_.Hom.hom
    (ModuleFunctor.SeparableAction.average_moduleHom
      (DiagonalAlgebra.canonicalSeparableNoPivotal S) (diagonalModuleHom S T τ))

/-- Averaging commutes with postcomposition by any actual module map. -/
lemma averageNative_comp {F G H : Ordinary C M N} (τ : F ⟶ G) (σ : G ⟶ H)
    [ModuleFunctor.IsModuleNatural C σ] :
    averageNative S T τ ≫ σ = averageNative S T (τ ≫ σ) := by
  exact congrArg Mod_.Hom.hom
    (ModuleFunctor.SeparableAction.average_comp
      (DiagonalAlgebra.canonicalSeparableNoPivotal S)
      (X := diagonalModule S T F) (Y := diagonalModule S T G)
      (Z := diagonalModule S T H) τ (diagonalModuleHom S T σ))

/-- An actual ordinary section of an actual module map remains a section
after genuine separable averaging. -/
lemma averageNative_section {F G : Ordinary C M N} (τ : F ⟶ G)
    [ModuleFunctor.IsModuleNatural C τ] (s : G ⟶ F) (hs : s ≫ τ = 𝟙 G) :
    averageNative S T s ≫ τ = 𝟙 G := by
  letI : ModuleFunctor.IsModuleNatural C (𝟙 G : G ⟶ G) :=
    inferInstanceAs (ModuleFunctor.IsModuleNatural C (𝟙 (toFunctor G)))
  rw [averageNative_comp, hs, averageNative_moduleHom]

end Paper18.Category.CentralFunctorAdjointSeparable
