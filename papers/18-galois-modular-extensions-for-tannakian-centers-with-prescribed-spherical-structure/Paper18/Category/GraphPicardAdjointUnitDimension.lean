import Paper18.Category.AdjointUnitFPDimension
import Paper18.Category.GraphPicardRightCentralDominant
import Paper18.Category.GraphPicardMoritaAlgebraMono
import Paper18.Category.GraphPicardMoritaClassificationDimensions
import Paper18.Category.GraphLagrangianDimension
import Paper18.Category.DrinfeldNoPivotalDimension
import Paper18.Category.SeparableAlgebraQuotient

/-! # The actual graph algebra equals the actual right-adjoint unit -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction BigOperators
universe v u w
namespace Paper18.Category.GraphPicard
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  (α : D ⥤ D) [α.Braided] [α.Additive] [α.Linear ℂ] [α.IsEquivalence]
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
local notation "M" => GraphLagrangian.ModuleOrbit S α
local notation "E" => ModuleAlphaInduction.End Dᴹᵒᵖ M
local notation "SC" => DrinfeldCoendModules.centerSkeletonNoPivotal S
local instance endKernels : HasKernels E := graphEndHasKernels S α
local instance endFiniteHom (F G : E) : FiniteDimensional ℂ (F ⟶ G) := graphEndFiniteHom S α F G
local instance endRightRigid : RightRigidCategory E := graphEndRightRigid S α
local instance endSimpleUnit : Simple (𝟙_ E) := graphEndSimpleUnit S α

include hD in
/-- Genuine dominance, the actual center-square formula and actual orbit
dimension determine the adjoint-unit dimension without separability. -/
theorem graphAdjointUnit_fpdim :
    (SC).fpdim (graphAdjointUnit S α) = S.fusionBasis.totalFPdim := by
  have hq := (SC).totalFPdim_eq_semisimpleAdjointAlgebra (graphEndSkeleton S α)
    (graphCentralUnderlying S α) (graphRightCentralAction_retract_dominant S α hD)
  change (SC).fusionBasis.totalFPdim =
    (SC).fpdim (graphAdjointUnit S α) * (graphEndFusionBasis S α).totalFPdim at hq
  rw [DrinfeldCoendModules.constructed_center_totalFPdim_noPivotal S,
    graphEnd_totalFPdim S α] at hq
  have hp : 0 < S.fusionBasis.totalFPdim :=
    Finset.sum_pos' (fun i _ => sq_nonneg (S.fusionBasis.fpdim i))
      ⟨S.unitLabel, Finset.mem_univ _, sq_pos_of_pos (S.fusionBasis.fpdim_pos _)⟩
  nlinarith

/-- The actual monic algebra map has equal actual FP dimensions and is
therefore an isomorphism of its actual underlying objects. -/
def graphAlgebraToAdjointUnitIsIso : IsIso (graphAlgebraToAdjointUnit S α) := by
  letI := graphAlgebraToAdjointUnit_mono S α hD
  apply (SC).isIso_of_mono_fpdim_eq (graphAlgebraToAdjointUnit S α)
  rw [GraphLagrangian.fpdim S α SC, graphAdjointUnit_fpdim S α hD]

/-- The true graph algebra identifies with the true adjoint-unit algebra. -/
def graphAlgebraAdjointUnitIso : GraphLagrangian.algebra S α ≅ graphAdjointUnit S α := by
  letI := graphAlgebraToAdjointUnitIsIso S α hD
  exact asIso (graphAlgebraToAdjointUnit S α)

@[simp] theorem graphAlgebraAdjointUnitIso_hom :
    (graphAlgebraAdjointUnitIso S α hD).hom = graphAlgebraToAdjointUnit S α := rfl

instance graphAlgebraAdjointUnitIsoHomMonHom :
    IsMonHom (graphAlgebraAdjointUnitIso S α hD).hom := by
  change IsMonHom (graphAlgebraToAdjointUnit S α)
  infer_instance

instance graphAlgebraAdjointUnitIsoInvMonHom :
    IsMonHom (graphAlgebraAdjointUnitIso S α hD).inv := by
  infer_instance

/-- Actual separability of the adjoint unit follows by pushing the
genuine graph separability element through the proved algebra isomorphism. -/
def graphAdjointUnitSeparable : SeparableAlgebra (graphAdjointUnit S α) := by
  letI := graphAlgebraToAdjointUnitIsIso S α hD
  exact SeparableAlgebra.quotient (graphAlgebraToAdjointUnit S α)
    (GraphLagrangian.separableNoPivotal S α)

end Paper18.Category.GraphPicard
