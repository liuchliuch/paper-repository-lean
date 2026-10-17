import Paper18.Category.GraphPicardMoritaGraphAdjoint
import Paper18.Category.NondegenerateBraidedFunctor
import Paper18.Category.FiniteSemisimpleLeftRigid
import Paper18.Category.DrinfeldNoPivotalNondegenerate
import Paper18.Category.RelativeTensorCentralImage

/-! # Actual full faithfulness of the genuine Morita central lift

The source is the actual nondegenerate center. Left rigidity of the
actual finite semisimple module-endofunctor target is derived from its
actual right duals. No target braiding or pivotal structure is used.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite MonoidalLeftAction
universe v u w vM uM t
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction Dᴹᵒᵖ M]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : Dᴹᵒᵖ, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ m : M, (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).Additive]
  [∀ m : M, (MonoidalLeftAction.actionRight Dᴹᵒᵖ m).Linear ℂ]
  [HasKernels (ModuleAlphaInduction.End Dᴹᵒᵖ M)]
  [HasFiniteBiproducts (ModuleAlphaInduction.End Dᴹᵒᵖ M)]
  [∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ M, FiniteDimensional ℂ (F ⟶ G)]
  [RightRigidCategory (ModuleAlphaInduction.End Dᴹᵒᵖ M)]
  [Simple (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ M))]
  {κ : Type t} [Fintype κ]
  (T : FiniteSemisimpleSkeleton (ModuleAlphaInduction.End Dᴹᵒᵖ M) κ)

/-- Actual finite semisimplicity and the actual simple component unit
suffice for the genuine central lift to be fully faithful. -/
def rightCentralLiftFullyFaithful : (rightCentralLift D M).FullyFaithful := by
  letI := FiniteSemisimpleLeftRigid.leftRigidCategory T
  have hZ : IsNondegenerate (C := Center D) := DrinfeldNoPivotal.center_nondegenerate S
  have hRev : @IsNondegenerate (Center D) _ _ (reverseBraiding (Center D)) _ _ :=
    RelativeTensor.nondegenerate_reverse_iff.mpr hZ
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI : (rightCentralLift D M).Braided := rightCentralLiftReverseBraided D M
  exact NondegenerateBraidedFunctor.fullyFaithful
    (DrinfeldCoendModules.centerSkeletonNoPivotal S) (rightCentralLift D M) hRev

end Paper18.Category.GraphPicard

namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The genuine central action on the actual graph orbit is actually
fully faithful after retaining its actual center structure. -/
def graphCentralLiftFullyFaithful :
    (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).FullyFaithful := by
  let R := GraphLagrangian.underlyingSeparableNoPivotal S α
  let hR := GraphLagrangian.underlying_id_ne_zero S α
  letI := R.orbitEndHasKernels S hR
  letI (F G : ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
    R.orbitEndFiniteHom S hR F G
  letI := graphEndRightRigid S α
  letI := graphEndSimpleUnit S α
  exact rightCentralLiftFullyFaithful S (GraphLagrangian.ModuleOrbit S α)
    (graphEndSkeleton S α)

end Paper18.Category.GraphPicard
