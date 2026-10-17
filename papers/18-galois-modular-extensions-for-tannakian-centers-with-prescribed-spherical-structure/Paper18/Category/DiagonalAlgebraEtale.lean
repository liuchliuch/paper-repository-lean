import Paper18.Category.DiagonalAlgebraDimension
import Paper18.Category.DiagonalAlgebraTwist
import Paper18.Category.DiagonalAlgebraSeparableRibbon

/-! # The actual connected étale diagonal algebra

Every finite braided spherical fusion category, including a degenerate one,
supplies the actual diagonal algebra, its perfect multiplication pairing,
its trivial prescribed twist, positive actual dimension, and normalized
actual bimodule separability section.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj
universe v u w
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hJ : J.Spherical)

/-- The actual normalized counit of the diagonal multiplication pairing. -/
lemma canonicalPairing_one_counit :
    η[canonicalAlgebra S] ≫ (canonicalMultiplicationPairing S).counit = 𝟙 _ := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  exact one_connectedCounit (DeligneProduct.skeleton S S)
    (semisimpleAdjointAlgebra (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C)))
    (semisimpleAdjointAlgebra_connected (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C)))

/-- The actual diagonal algebra is separable: the section and both
bimodule identities are derived from the actual perfect pairing and the
strictly positive actual categorical dimension. -/
def canonicalSeparable : SeparableAlgebra (canonicalAlgebra S) := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  letI := canonicalAlgebra_commutative S
  exact separableOfTrivialTwist (canonicalMultiplicationPairing S)
    (Drinfeld.reverseSecondPivotal J) (canonicalAlgebra_connected S)
    (canonicalPairing_one_counit S) (canonicalAlgebra_twist S J hJ)
    (canonicalAlgebra_rightDim_ne_zero S J)

end Paper18.Category.DiagonalAlgebra
