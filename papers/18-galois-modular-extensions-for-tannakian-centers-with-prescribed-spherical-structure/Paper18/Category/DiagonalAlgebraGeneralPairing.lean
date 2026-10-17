import Paper18.Category.DiagonalAlgebraGeneralDecomposition
import Paper18.Category.DiagonalAlgebraPerfect
import Paper18.Category.LinearTensorRigid
import Paper18.Category.LinearMatMonoidalRigid

/-! # The actual nondegenerate multiplication pairing of the general diagonal -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
universe v u w
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The canonical diagonal algebra has an actual perfect multiplication
pairing, with an actual central counit and both actual snake identities.
No nondegeneracy or chosen spherical structure is assumed. -/
def canonicalMultiplicationPairing : ModuleBalancing.MultiplicationPairing (canonicalAlgebra S) := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  exact adjointMultiplicationPairing (DeligneProduct.skeleton S S) S (tensorProductFunctor (C := C))

end Paper18.Category.DiagonalAlgebra
