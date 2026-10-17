import Paper18.Category.GraphPicardOrbitAlphaEssSurjNondegenerate

/-! # Actual strong central-sign equivalences of the graph orbit

The two actions here have source D and target the actual End category.
Their tensorators come from the actual right central action. The native
alpha functors have source Dᴹᵒᵖ and the opposite signs.
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
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

abbrev graphPositiveOrbitAction :=
  Drinfeld.positive D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α)
abbrev graphNegativeOrbitAction :=
  Drinfeld.negative D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α)

def graphPositiveOrbitActionIsEquivalence :
    (graphPositiveOrbitAction S α).IsEquivalence := by
  letI := graphNegativeIsEquivalenceOfNondegenerate S α hD
  letI : (mopFunctor D ⋙ graphNegative S α).IsEquivalence := inferInstance
  exact Functor.isEquivalence_of_iso
    (rightPositiveNativeIso D (GraphLagrangian.ModuleOrbit S α)).symm

def graphNegativeOrbitActionIsEquivalence :
    (graphNegativeOrbitAction S α).IsEquivalence := by
  letI := graphPositiveIsEquivalenceOfNondegenerate S α hD
  letI : (mopFunctor D ⋙ graphPositive S α).IsEquivalence := inferInstance
  exact Functor.isEquivalence_of_iso
    (rightNegativeNativeIso D (GraphLagrangian.ModuleOrbit S α)).symm

/-- The actual positive central-sign action, with its genuine strong
tensor structure, is an actual equivalence. -/
def graphPositiveActionEquivalence :
    D ≌ ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α) := by
  letI := graphPositiveOrbitActionIsEquivalence S α hD
  exact (graphPositiveOrbitAction S α).asEquivalence

/-- The corresponding actual negative central-sign equivalence. -/
def graphNegativeActionEquivalence :
    D ≌ ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α) := by
  letI := graphNegativeOrbitActionIsEquivalence S α hD
  exact (graphNegativeOrbitAction S α).asEquivalence

instance graphPositiveActionFunctorMonoidal :
    (graphPositiveActionEquivalence S α hD).functor.Monoidal :=
  inferInstanceAs (graphPositiveOrbitAction S α).Monoidal
instance graphNegativeActionFunctorMonoidal :
    (graphNegativeActionEquivalence S α hD).functor.Monoidal :=
  inferInstanceAs (graphNegativeOrbitAction S α).Monoidal

instance graphPositiveActionInverseMonoidal :
    (graphPositiveActionEquivalence S α hD).inverse.Monoidal :=
  (graphPositiveActionEquivalence S α hD).inverseMonoidal
instance graphNegativeActionInverseMonoidal :
    (graphNegativeActionEquivalence S α hD).inverse.Monoidal :=
  (graphNegativeActionEquivalence S α hD).inverseMonoidal

instance graphPositiveActionEquivalenceMonoidal :
    (graphPositiveActionEquivalence S α hD).IsMonoidal := by infer_instance
instance graphNegativeActionEquivalenceMonoidal :
    (graphNegativeActionEquivalence S α hD).IsMonoidal := by infer_instance

end Paper18.Category.GraphPicard
