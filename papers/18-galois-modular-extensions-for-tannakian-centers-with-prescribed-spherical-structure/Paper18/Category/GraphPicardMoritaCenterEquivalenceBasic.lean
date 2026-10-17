import Paper18.Category.GraphPicardAssociatedBraided
import Paper18.Category.GraphPicardDimension
import Paper18.Category.GraphPicardMoritaCentralFullyFaithful
import Paper18.Category.DrinfeldNoPivotalDimension
import Paper18.Category.DrinfeldEquivalenceMapLinear
import Paper18.Category.FactorizationEssentialSurjectiveBasic

/-! # Actual fusion foundations for the graph dual's center

The actual central-sign tensor equivalence induces a genuine equivalence
between the two centers. Transporting the proved no-pivotal center skeleton
along it constructs the target center skeleton. No braiding on the module
endofunctor category, center semisimplicity certificate or numerical equality
is needed. This auxiliary center equivalence supplies foundations for proving
essential surjectivity of the original Morita central lift.
-/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits MonoidalOpposite
open scoped MonObj MonoidalLeftAction
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

/-- An auxiliary braiding can indeed be transferred through the actual
tensor equivalence. The center construction below does not require it. -/
def graphMoritaEndBraiding : BraidedCategory
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
  BraidedCategory.ofFullyFaithful (graphPositiveActionEquivalence S α hD).inverse

local instance moritaCenterEndKernels : HasKernels
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) := graphEndHasKernels S α
local instance moritaCenterEndFiniteHom (F G : ModuleAlphaInduction.End Dᴹᵒᵖ
    (GraphLagrangian.ModuleOrbit S α)) : FiniteDimensional ℂ (F ⟶ G) := graphEndFiniteHom S α F G
local instance moritaCenterEndRightRigid : RightRigidCategory
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) := graphEndRightRigid S α
local instance moritaCenterEndSimpleUnit : Simple
    (𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))) := graphEndSimpleUnit S α
local instance moritaCenterEndLeftRigid : LeftRigidCategory
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
  FiniteSemisimpleLeftRigid.leftRigidCategory (graphEndSkeleton S α)

local instance moritaCenterFiniteHom
    (X Y : Center (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α))) :
    FiniteDimensional ℂ (X ⟶ Y) := by
  letI : ∀ F G : ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α),
      FiniteDimensional ℂ (F ⟶ G) := graphEndFiniteHom S α
  exact Drinfeld.hom_finiteDimensional X Y

/-- Genuine center transport along the already proved actual tensor
equivalence. Its underlying functor is not identified with the Morita lift. -/
def graphMoritaAuxiliaryCenterEquivalence : Center D ≌
    Center (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
  DrinfeldEquivalence.equivalence (graphPositiveActionEquivalence S α hD).functor

instance graphMoritaAuxiliaryCenterFunctorMonoidal :
    (graphMoritaAuxiliaryCenterEquivalence S α hD).functor.Monoidal :=
  inferInstanceAs (DrinfeldEquivalence.map (graphPositiveActionEquivalence S α hD).functor).Monoidal
instance graphMoritaAuxiliaryCenterFunctorAdditive :
    (graphMoritaAuxiliaryCenterEquivalence S α hD).functor.Additive :=
  inferInstanceAs (DrinfeldEquivalence.map (graphPositiveActionEquivalence S α hD).functor).Additive
instance graphMoritaAuxiliaryCenterFunctorLinear :
    (graphMoritaAuxiliaryCenterEquivalence S α hD).functor.Linear ℂ :=
  inferInstanceAs ((DrinfeldEquivalence.map (graphPositiveActionEquivalence S α hD).functor).Linear ℂ)
instance graphMoritaAuxiliaryCenterInverseMonoidal :
    (graphMoritaAuxiliaryCenterEquivalence S α hD).inverse.Monoidal :=
  (graphMoritaAuxiliaryCenterEquivalence S α hD).inverseMonoidal

/-- Actual simple labels transported from the constructed source center. -/
abbrev GraphMoritaCenterSimpleIndex := DrinfeldCoendModules.CenterSimpleIndexNoPivotal S

/-- The actual finite semisimple skeleton of the graph dual's center.
No center semisimplicity or existence certificate is supplied. -/
def graphMoritaCenterSkeleton : FiniteSemisimpleSkeleton
    (Center (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)))
    (GraphMoritaCenterSimpleIndex S) :=
  DrinfeldCoendModules.SkeletonTransport.skeleton
    (graphMoritaAuxiliaryCenterEquivalence S α hD).functor
    (DrinfeldCoendModules.centerSkeletonNoPivotal S)

/-- The actual fusion basis of the graph dual's actual center. -/
def graphMoritaCenterFusionBasis : FusionBasis (GraphMoritaCenterSimpleIndex S) :=
  (graphMoritaCenterSkeleton S α hD).fusionBasis

/-- Actual monoidal equivalences in both directions give equality of the
intrinsic source and target center dimensions. -/
theorem graphMoritaCenter_totalFPdim_eq :
    (DrinfeldCoendModules.centerSkeletonNoPivotal S).fusionBasis.totalFPdim =
      (graphMoritaCenterSkeleton S α hD).fusionBasis.totalFPdim := by
  let ZS := DrinfeldCoendModules.centerSkeletonNoPivotal S
  let ZT := graphMoritaCenterSkeleton S α hD
  let e := graphMoritaAuxiliaryCenterEquivalence S α hD
  exact le_antisymm (ZS.totalFPdim_le_of_fullyFaithful ZT e.functor)
    (ZT.totalFPdim_le_of_fullyFaithful ZS e.inverse)

/-- The proved no-pivotal source center dimension square computes the
actual graph dual center's intrinsic total dimension. -/
theorem graphMoritaCenter_totalFPdim :
    (graphMoritaCenterFusionBasis S α hD).totalFPdim = S.fusionBasis.totalFPdim ^ 2 := by
  change (graphMoritaCenterSkeleton S α hD).fusionBasis.totalFPdim = _
  rw [← graphMoritaCenter_totalFPdim_eq S α hD]
  exact DrinfeldCoendModules.constructed_center_totalFPdim_noPivotal S

/-- In particular the actual graph dual center has the square of the
actual graph dual's intrinsic total FP dimension. -/
theorem graphMoritaCenter_totalFPdim_eq_end_square :
    (graphMoritaCenterFusionBasis S α hD).totalFPdim = (graphEndFusionBasis S α).totalFPdim ^ 2 := by
  rw [graphEnd_totalFPdim S α]
  exact graphMoritaCenter_totalFPdim S α hD

end Paper18.Category.GraphPicard
