import Paper18.Category.DiagonalAlgebraCapGenerator

/-! # Actual dinaturality of canonical diagonal cap generators -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.DiagonalAlgebra
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual adjunction-transpose generators are dinatural in their
object: moving a morphism across a cap takes its actual right dual mate. -/
lemma capGenerator_dinaturality {X Y : D} (f : X ⟶ Y) :
    capPairMap (dualMap D f) (𝟙 X) ≫ capGenerator S X =
      capPairMap (𝟙 (dual D Y)) f ≫ capGenerator S Y := by
  apply ((tensorProductRightAdjunction S).homEquiv _ _).symm.injective
  change (tensorProductFunctor (C := D)).map
      (capPairMap (dualMap D f) (𝟙 X) ≫ capGenerator S X) ≫ canonicalAlgebraCounit S =
    (tensorProductFunctor (C := D)).map
      (capPairMap (𝟙 (dual D Y)) f ≫ capGenerator S Y) ≫ canonicalAlgebraCounit S
  simp only [Functor.map_comp, assoc]
  rw [capGenerator_counit, capGenerator_counit, capPairIso_naturality_assoc,
    capPairIso_naturality_assoc]
  simp only [tensorHom_id, id_tensorHom]
  rw [rightAdjointMate_comp_evaluation]

end Paper18.Category.DiagonalAlgebra
