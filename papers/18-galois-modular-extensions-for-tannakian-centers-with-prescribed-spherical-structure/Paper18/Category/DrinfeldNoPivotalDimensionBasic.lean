import Paper18.Category.DrinfeldCoendModulesInverse
import Paper18.Category.RelativeTensorAdjunction
import Paper18.Category.DrinfeldExact
import Paper18.Category.DrinfeldRigid

/-! # The actual internal coend's FP dimension without pivotal data -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual separable internal coend has the ambient total FP dimension. -/
theorem algebra_fpdim : S.fpdim (algebra S) = S.fusionBasis.totalFPdim :=
  DiagonalAlgebra.mappedCanonicalAlgebra_fpdim S
    (DiagonalAlgebra.tensorProductFunctor (C := D)) S

/-- Actual free coend modules have the expected underlying FP dimension. -/
theorem free_underlying_fpdim (X : D) :
    S.fpdim (InternalModule.free (algebra S) X).X =
      S.fusionBasis.totalFPdim * S.fpdim X := by
  change S.fpdim (algebra S ⊗ X) = _
  rw [S.fpdim_tensor, algebra_fpdim S]

end Paper18.Category.DrinfeldCoendModules
