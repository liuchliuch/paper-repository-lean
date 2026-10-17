import Paper18.Category.GraphLagrangianBasic
import Paper18.Category.DrinfeldSemisimple
import Paper18.Category.DrinfeldDimension

/-! # Actual FP dimensions of graph algebras

The graph's FP dimension is computed from the actual strong monoidal
functor. The dimension-square theorem is separately exposed when an actual
ambient pivotal structure supplies the constructed center skeleton.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.GraphLagrangian
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
  {κ : Type t} [Fintype κ] (T : FiniteSemisimpleSkeleton (Center D) κ)

/-- For any actual complete finite center skeleton, its intrinsic FP
character assigns the actual graph algebra dimension equal to FPdim(D).
No pivotal structure or dimension equation is an assumption. -/
theorem fpdim : T.fpdim (algebra S α) = S.fusionBasis.totalFPdim :=
  DiagonalAlgebra.mappedCanonicalAlgebra_fpdim S (graphFunctor α) T

variable (J : PivotalStructure D)

/-- An actual ambient pivotal structure constructs the actual center's
complete finite skeleton and proves its total dimension-square formula. -/
theorem center_totalFPdim :
    (Drinfeld.centerSkeleton S J).fusionBasis.totalFPdim = S.fusionBasis.totalFPdim ^ 2 :=
  Drinfeld.center_totalFPdim S J (Drinfeld.centerSkeleton S J)

/-- For the constructed actual center skeleton, the actual graph dimension
saturates the actual dimension-square relation. -/
theorem dimension_square :
    ((Drinfeld.centerSkeleton S J).fpdim (algebra S α)) ^ 2 =
      (Drinfeld.centerSkeleton S J).fusionBasis.totalFPdim := by
  rw [fpdim S α (Drinfeld.centerSkeleton S J), center_totalFPdim S J]

end Paper18.Category.GraphLagrangian
