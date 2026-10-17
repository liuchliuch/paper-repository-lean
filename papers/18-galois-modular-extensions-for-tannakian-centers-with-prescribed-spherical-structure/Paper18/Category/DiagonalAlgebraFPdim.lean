import Paper18.Category.DiagonalAlgebraGeneralDecomposition

/-! # Intrinsic FP dimension of the actual canonical diagonal algebra -/
noncomputable section
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.DiagonalAlgebra
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- The actual diagonal algebra has intrinsic FP dimension equal to the
actual total FP dimension of the shared category. -/
theorem canonicalAlgebra_fpdim :
    letI := DeligneProduct.hasKernels S S
    letI := DeligneProduct.simpleUnit S S
    (DeligneProduct.skeleton S S).fpdim (canonicalAlgebra S) = S.fusionBasis.totalFPdim := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  let P := DeligneProduct.skeleton S S
  have hp (i : ι) : P.fpdim (DeligneProduct.pairObject S S i (S.dualLabel i)) =
      S.fusionBasis.fpdim i * S.fusionBasis.fpdim (S.dualLabel i) := by
    change P.fpdim (P.simpleObject (i, S.dualLabel i)) = _
    rw [P.fpdim_simple, DeligneProduct.fpdim_pair]
  rw [P.fpdim_iso (canonicalAlgebraIso S)]
  unfold diagonalObject
  rw [P.fpdim_biproduct]
  simp_rw [hp]
  change (∑ i, S.fusionBasis.fpdim i * S.fusionBasis.fpdim (S.fusionBasis.dual i)) = _
  simp only [S.fusionBasis.fpdim_dual]
  exact Finset.sum_congr rfl (fun i _ => (pow_two _).symm)

end Paper18.Category.DiagonalAlgebra
