import Paper18.Category.DiagonalAlgebraGeneralPairing
import Paper18.Category.DiagonalAlgebraFiniteReindex
import Paper18.Category.DrinfeldPivotalFactorization
import Paper18.Category.ModuleBalancingPositive

/-! # The actual positive categorical dimension of the canonical diagonal -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped BigOperators
universe v u w
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [RightRigidCategory C] [Preadditive C] [Linear ℂ C]
  [MonoidalPreadditive C] [MonoidalLinear ℂ C] [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ C)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι) (J : PivotalStructure C)

/-- The actual tensor-product functor preserves the prescribed product
pivotal structure, by the two actual center preservation theorems. -/
theorem tensorProductFunctor_preservesPivotal :
    PreservesPivotal (tensorProductFunctor (C := C)) (Drinfeld.reverseSecondPivotal J) J :=
  (Drinfeld.deligneFactorization_preservesPivotal J).comp (Drinfeld.forget_preservesPivotal J)

/-- The actual diagonal algebra's prescribed categorical dimension equals
the actual global dimension; no nondegeneracy or positivity input is used. -/
theorem canonicalAlgebra_rightDim :
    letI := DeligneProduct.hasKernels S S
    letI := DeligneProduct.simpleUnit S S
    (Drinfeld.reverseSecondPivotal J).rightDim (canonicalAlgebra S) =
      (J.pivotalData S).globalDimension := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  let F := tensorProductFunctor (C := C)
  let K := Drinfeld.reverseSecondPivotal J
  have hp := tensorProductFunctor_preservesPivotal J
  let e : diagonalObject S ≅ ⨁ fun a : Fin (Fintype.card ι) =>
      DeligneProduct.pairObject S S ((Fintype.equivFin ι).symm a)
        (S.dualLabel ((Fintype.equivFin ι).symm a)) := by
    unfold diagonalObject
    exact (biproductReindex (Fintype.equivFin ι).symm
      (fun i : ι => DeligneProduct.pairObject S S i (S.dualLabel i))).symm
  have hpair (i : ι) : J.rightDim (F.obj (DeligneProduct.pairObject S S i (S.dualLabel i))) =
      J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject (S.dualLabel i)) := by
    erw [J.rightDim_iso ((Center.forget C).mapIso
      (Drinfeld.deligneFactorizationPairIso (S.simpleObject i) (S.simpleObject (S.dualLabel i))))]
    exact J.rightDim_tensor _ _
  calc
    K.rightDim (canonicalAlgebra S) = J.rightDim (F.obj (canonicalAlgebra S)) :=
      (hp.rightDim_scalar _).symm
    _ = J.rightDim (F.obj (diagonalObject S)) := J.rightDim_iso (F.mapIso (canonicalAlgebraIso S))
    _ = J.rightDim (F.obj (⨁ fun a : Fin (Fintype.card ι) =>
        DeligneProduct.pairObject S S ((Fintype.equivFin ι).symm a)
          (S.dualLabel ((Fintype.equivFin ι).symm a)))) :=
      J.rightDim_iso (F.mapIso e)
    _ = J.rightDim (⨁ fun a : Fin (Fintype.card ι) => F.obj
        (DeligneProduct.pairObject S S ((Fintype.equivFin ι).symm a)
          (S.dualLabel ((Fintype.equivFin ι).symm a)))) := J.rightDim_iso (F.mapBiproduct _)
    _ = ∑ a : Fin (Fintype.card ι), J.rightDim (F.obj
        (DeligneProduct.pairObject S S ((Fintype.equivFin ι).symm a)
          (S.dualLabel ((Fintype.equivFin ι).symm a)))) := J.rightDim_biproduct _
    _ = ∑ a : Fin (Fintype.card ι), J.rightDim (S.simpleObject ((Fintype.equivFin ι).symm a)) *
        J.rightDim (S.simpleObject (S.dualLabel ((Fintype.equivFin ι).symm a))) := by simp_rw [hpair]
    _ = ∑ i : ι, J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject (S.dualLabel i)) :=
      (Fintype.equivFin ι).symm.sum_comp (fun i : ι =>
        J.rightDim (S.simpleObject i) * J.rightDim (S.simpleObject (S.dualLabel i)))
    _ = _ := rfl

/-- The diagonal's actual prescribed categorical dimension is strictly
positive in real part, derived from actual simple norm dimensions. -/
theorem canonicalAlgebra_rightDim_re_pos :
    letI := DeligneProduct.hasKernels S S
    letI := DeligneProduct.simpleUnit S S
    0 < ((Drinfeld.reverseSecondPivotal J).rightDim (canonicalAlgebra S)).re := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  rw [canonicalAlgebra_rightDim S J]
  exact (J.pivotalData S).globalDimension_re_pos

/-- The actual diagonal dimension is real, since every actual simple norm
is real. Together with the strict positive real part this is positivity. -/
theorem canonicalAlgebra_rightDim_im_eq_zero :
    letI := DeligneProduct.hasKernels S S
    letI := DeligneProduct.simpleUnit S S
    ((Drinfeld.reverseSecondPivotal J).rightDim (canonicalAlgebra S)).im = 0 := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  rw [canonicalAlgebra_rightDim S J]
  simp [Paper18.PivotalData.globalDimension, (J.pivotalData S).ndim_eq_normSq]

/-- Its actual categorical dimension is nonzero. -/
theorem canonicalAlgebra_rightDim_ne_zero :
    letI := DeligneProduct.hasKernels S S
    letI := DeligneProduct.simpleUnit S S
    (Drinfeld.reverseSecondPivotal J).rightDim (canonicalAlgebra S) ≠ 0 := by
  letI := DeligneProduct.hasKernels S S
  letI := DeligneProduct.simpleUnit S S
  rw [canonicalAlgebra_rightDim S J]
  exact (J.pivotalData S).globalDimension_ne_zero

end Paper18.Category.DiagonalAlgebra
