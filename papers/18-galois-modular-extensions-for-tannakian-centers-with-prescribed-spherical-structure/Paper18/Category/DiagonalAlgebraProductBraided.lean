import Paper18.Category.DiagonalAlgebraProduct
import Paper18.Category.DeligneProductMapReverse

/-! # Commutativity of the actual ambient shared diagonal algebra -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u w vN uN vP uP
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {N : Type uN} [Category.{vN} N] [MonoidalCategory N] [BraidedCategory N]
  [Preadditive N] [Linear ℂ N] [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  {P : Type uP} [Category.{vP} P] [MonoidalCategory P] [BraidedCategory P]
  [Preadditive P] [Linear ℂ P] [MonoidalPreadditive P] [MonoidalLinear ℂ P]
  (F : C ⥤ N) [F.Braided] [F.Additive] [F.Linear ℂ]
  (G : C ⥤ P) [G.Braided] [G.Additive] [G.Linear ℂ]

/-- The actual ambient diagonal is commutative for the actual
reverse-second target braiding. All braidings remain explicit. -/
def productCanonicalAlgebra_commutative :
    letI : BraidedCategory (DeligneProduct N P) := DeligneProduct.reverseSecondBraiding N P
    IsCommMonObj (productCanonicalAlgebra S F G) := by
  letI : BraidedCategory (DeligneProduct N P) := DeligneProduct.reverseSecondBraiding N P
  letI : BraidedCategory (DeligneProduct C C) := Drinfeld.deligneReverseSecondBraiding C
  letI : (DeligneProduct.map F G).Braided := DeligneProduct.mapReverseSecondBraided F G
  exact mappedCanonicalAlgebra_commutative S (DeligneProduct.map F G)
    (fun X Y => Functor.LaxBraided.braided (F := DeligneProduct.map F G) X Y)

end Paper18.Category.DiagonalAlgebra
