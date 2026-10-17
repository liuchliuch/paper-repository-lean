import Paper18.Category.DiagonalAlgebraGeneral
import Paper18.Category.DiagonalAlgebraDecomposition

/-! # The genuine diagonal decomposition without nondegeneracy assumptions -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)

/-- Actual simple-pair multiplicities of the general canonical algebra. -/
theorem canonicalAlgebra_multiplicity (i j : ι) :
    Module.finrank ℂ (DeligneProduct.pairObject S S i j ⟶ canonicalAlgebra S) =
      if i = S.dualLabel j then 1 else 0 := by
  letI := DeligneProduct.hasKernels S S
  change Module.finrank ℂ ((DeligneProduct.skeleton S S).simpleObject (i,j) ⟶
    semisimpleRightAdjointObj (DeligneProduct.skeleton S S) (tensorProductFunctor (C := C)) (𝟙_ C)) = _
  rw [finrank_rightAdjointObj]
  calc
    _ = Module.finrank ℂ (S.simpleObject i ⊗ S.simpleObject j ⟶ 𝟙_ C) :=
      finrank_hom_iso ((Center.forget C).mapIso
        (Drinfeld.deligneFactorizationPairIso (S.simpleObject i) (S.simpleObject j))) (Iso.refl _)
    _ = Module.finrank ℂ (S.simpleObject i ⟶ (S.simpleObject j)ᘁ) := by
      rw [(tensorRightHomLinearEquiv (S.simpleObject i) (S.simpleObject j)
        ((S.simpleObject j)ᘁ) (𝟙_ C)).finrank_eq]
      exact finrank_hom_iso (Iso.refl _) (λ_ ((S.simpleObject j)ᘁ))
    _ = Module.finrank ℂ (S.simpleObject i ⟶ S.simpleObject (S.dualLabel j)) :=
      finrank_hom_iso (Iso.refl _) (S.dualIso j).symm
    _ = _ := S.finrank_simple_hom_simple i (S.dualLabel j)

/-- The actual Hom-coordinate isomorphism to the genuine diagonal sum. -/
def canonicalCoordinatesIso :
    (DeligneProduct.coordinates S S).obj (canonicalAlgebra S) ≅
      (DeligneProduct.coordinates S S).obj (diagonalObject S) where
  hom p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    ((canonicalAlgebra_multiplicity S p.1 p.2).trans
      (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.hom
  inv p := (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
    ((canonicalAlgebra_multiplicity S p.1 p.2).trans
      (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.inv
  hom_inv_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      ((canonicalAlgebra_multiplicity S p.1 p.2).trans
        (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.hom_inv_id
  inv_hom_id := by
    funext p
    exact (Classical.choice (FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
      ((canonicalAlgebra_multiplicity S p.1 p.2).trans
        (diagonalObject_multiplicity S p.1 p.2).symm))).toFGModuleCatIso.inv_hom_id

/-- For every actual finite braided fusion category, the actual algebra
constructed from tensor product is the diagonal sum Σᵢ Sᵢ ⊠ Sᵢ*. -/
def canonicalAlgebraIso : canonicalAlgebra S ≅ diagonalObject S :=
  (DeligneProduct.coordinates S S).preimageIso (canonicalCoordinatesIso S)

end Paper18.Category.DiagonalAlgebra
