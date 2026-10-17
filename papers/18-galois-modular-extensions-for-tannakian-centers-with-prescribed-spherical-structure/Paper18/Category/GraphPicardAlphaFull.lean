import Paper18.Category.GraphPicardAlphaFullBasic
import Paper18.Category.GraphPicardAlphaCentral
import Paper18.Category.GraphPicardDimension
import Paper18.Category.GraphPicardMoritaCentralSigns
import Paper18.Category.GraphPicardMoritaImageCentralFullyFaithful

/-! # Actual fullness of both graph alpha-induction functors

The actual negative central lift restricts to the actual summand image.
Nondegeneracy proves that central restriction fully faithful. The genuine
opposite-action commutant makes every original image morphism central on
that image, so fullness descends to the original underlying functor.
-/
noncomputable section
set_option maxHeartbeats 2000000
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
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

instance graphNegativeCentralBraided : (graphNegativeCentral S α).Braided := by
  change (α ⋙ negativeCentralLift D (GraphLagrangian.ModuleOrbit S α)).Braided
  infer_instance

/-- Nondegeneracy makes the actual negative underlying graph action
full, after the given actual self-equivalence. No action or Azumaya
equivalence is supplied. -/
def graphNegativeActionFull (hD : IsNondegenerate (C := D)) :
    (α ⋙ Drinfeld.negative D ⋙ rightCentralAction D
      (GraphLagrangian.ModuleOrbit S α)).Full := by
  letI := graphEndHasKernels S α
  letI (F G : ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
    graphEndFiniteHom S α F G
  letI := graphEndRightRigid S α
  letI := graphEndSimpleUnit S α
  let K := graphNegativeCentral S α
  let L := graphPositiveCentral S α
  let ff := MoritaImage.centralCoreFullyFaithful S K (graphEndSkeleton S α) hD
  letI := ff.full
  exact fullUnderlyingOfCentralCore K L (graphCentralUnderlyingIso S α).symm
    (fun X Y => (graphCentral_cross S α Y X).symm)

/-- The actual ordinary cap isomorphism transports the derived fullness
to the positive underlying graph action. -/
def graphPositiveActionFull (hD : IsNondegenerate (C := D)) :
    (Drinfeld.positive D ⋙ rightCentralAction D
      (GraphLagrangian.ModuleOrbit S α)).Full := by
  letI := graphNegativeActionFull S α hD
  exact Functor.Full.of_iso (graphOrbitCapOrdinaryIso S α)

/-- Actual native positive alpha induction is full on the chosen actual
graph orbit. Source reindexings are genuine equivalences. -/
def graphPositiveFull (hD : IsNondegenerate (C := D)) : (graphPositive S α).Full := by
  let N := Drinfeld.negative D ⋙
    rightCentralAction D (GraphLagrangian.ModuleOrbit S α)
  letI : (α ⋙ N).Full := graphNegativeActionFull S α hD
  letI : N.Full := fullOfEquivalencePrecompose α N
  letI : (mopFunctor D ⋙ graphPositive S α).Full :=
    Functor.Full.of_iso (rightNegativeNativeIso D (GraphLagrangian.ModuleOrbit S α))
  exact fullOfEquivalencePrecompose (mopFunctor D) (graphPositive S α)

/-- Actual native negative alpha induction is full on the same actual
graph orbit, with the sign convention retained explicitly. -/
def graphNegativeFull (hD : IsNondegenerate (C := D)) : (graphNegative S α).Full := by
  letI := graphPositiveActionFull S α hD
  letI : (mopFunctor D ⋙ graphNegative S α).Full :=
    Functor.Full.of_iso (rightPositiveNativeIso D (GraphLagrangian.ModuleOrbit S α))
  exact fullOfEquivalencePrecompose (mopFunctor D) (graphNegative S α)

end Paper18.Category.GraphPicard
