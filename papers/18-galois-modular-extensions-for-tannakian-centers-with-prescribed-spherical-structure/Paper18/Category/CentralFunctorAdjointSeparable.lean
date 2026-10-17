import Paper18.Category.CentralFunctorAdjointSeparableModuleSemisimple
import Paper18.Category.CentralFunctorAdjointSeparableOpposite
import Paper18.Category.GraphPicardMoritaImageSemisimple

/-! # Actual separability of the right-adjoint unit algebra

The actual tensor image of a strong additive complex-linear functor has
an actual module-category equivalence and an actual finite semisimple
module skeleton. Diagonal averaging therefore gives a genuine bimodule
section of the right-adjoint unit multiplication. No dominance,
separability, pivotal structure, or module realization is assumed.

In particular this applies to the underlying functor of a genuine central
tensor functor, independently of the centrality used to prove commutativity.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj
universe v u w u' w'
namespace Paper18.Category.CentralFunctorAdjointSeparable
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasFiniteBiproducts C] [HasKernels C] [MonoidalCategory C] [BraidedCategory C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [RightRigidCategory C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {D : Type u'} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [HasFiniteBiproducts D] [HasKernels D] [MonoidalCategory D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (F : C ⥤ D) [F.Additive] [F.Linear ℂ] [F.Monoidal]
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton D κ)

/-- The actual right-adjoint unit algebra of an actual strong additive
linear functor is separable. The actual tensor image and the actual
module skeleton are constructed, and the actual bimodule section is
obtained by proved diagonal averaging. The target need not be braided,
rigid, or have simple unit; no pivotal structure is required. -/
def adjointUnitSeparable :
    SeparableAlgebra (DiagonalAlgebra.semisimpleAdjointAlgebra S F) := by
  classical
  letI : RightRigidCategory Cᴹᵒᵖ := MonoidalOppositeFusion.rightRigidCategory
  letI : Simple (𝟙_ Cᴹᵒᵖ) := MonoidalOppositeFusion.simpleUnit
  exact separableOfMop
    (separableOfModuleSemisimple (MonoidalOppositeFusion.skeleton S)
      (mop (DiagonalAlgebra.semisimpleAdjointAlgebra S F))
      (GraphPicard.MoritaImage.moduleSkeleton S F T))

end Paper18.Category.CentralFunctorAdjointSeparable
