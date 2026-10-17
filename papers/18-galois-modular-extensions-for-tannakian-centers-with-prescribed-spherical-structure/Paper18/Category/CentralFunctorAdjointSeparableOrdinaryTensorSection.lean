import Paper18.Category.CentralFunctorAdjointSeparableOrdinarySplitting
import Paper18.Category.CentralFunctorAdjointSeparableTensorMultiplication
import Paper18.Category.BimoduleRelativeTensorFunctorLinear
import Paper18.Category.SeparableModulesKernels
import Paper18.Category.SeparableModulesBiproducts

/-! # An actual ordinary section of the multiplication tensor map

Finite semisimplicity of the actual module category supplies an ordinary
natural section. The construction does not assume separability of the
algebra or module naturality of this section.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.CentralFunctorAdjointSeparable
open BimoduleRelativeTensor
variable {D : Type u} [Category.{v} D] [MonoidalCategory D]
  [HasCoequalizers D] [LeftRigidCategory D] [RightRigidCategory D]
  [Preadditive D] [Linear ℂ D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  (R : D) [MonObj R]
  {ι : Type w} [Fintype ι] (T : FiniteSemisimpleSkeleton (Mod_ D R) ι)
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual pointwise-epimorphic multiplication tensor transformation
has an ordinary natural section, obtained on module simples and extended
through their actual finite biproduct decompositions. -/
def ordinaryTensorMultiplicationSplit : SplitEpi (tensorMultiplication R) :=
  ordinarySplitEpi T T (tensorMultiplication R)

/-- The actual ordinary section to be averaged using the diagonal algebra. -/
def ordinaryTensorMultiplicationSection :
    tensorFunctor (ModuleFunctor.wattsRegular (R := R)) ⟶
      tensorFunctor (SeparableAlgebra.freeRegularBimodule R) :=
  (ordinaryTensorMultiplicationSplit R T).section_

/-- The ordinary section satisfies its actual splitting equation before
any averaging or separability conclusion is used. -/
@[reassoc (attr := simp)]
lemma ordinaryTensorMultiplicationSection_id :
    ordinaryTensorMultiplicationSection R T ≫ tensorMultiplication R = 𝟙 _ :=
  (ordinaryTensorMultiplicationSplit R T).id

end Paper18.Category.CentralFunctorAdjointSeparable
