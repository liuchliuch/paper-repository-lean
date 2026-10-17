import Paper18.Category.GraphPicardNativeRelation
import Paper18.Category.GraphPicardMoritaCentralLinear
import Paper18.Category.RelativeTensorCentralImage

/-! # The actual two central graph actions and their genuine commutant data -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
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

/-- The actual positive central lift on the actual graph orbit. Its
braided source convention is the reverse braiding of the original D. -/
def graphPositiveCentral : D ⥤ Center
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
  Drinfeld.positive D ⋙ rightCentralLift D (GraphLagrangian.ModuleOrbit S α)

/-- The actual negative central lift after the specified braided
self-equivalence, on the same genuine graph orbit. -/
def graphNegativeCentral : D ⥤ Center
    (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) :=
  α ⋙ Drinfeld.negative D ⋙ rightCentralLift D (GraphLagrangian.ModuleOrbit S α)

instance graphPositiveCentralMonoidal : (graphPositiveCentral S α).Monoidal := by
  unfold graphPositiveCentral; infer_instance
instance graphPositiveCentralAdditive : (graphPositiveCentral S α).Additive := by
  unfold graphPositiveCentral; infer_instance
instance graphPositiveCentralLinear : (graphPositiveCentral S α).Linear ℂ := by
  unfold graphPositiveCentral; infer_instance
instance graphNegativeCentralMonoidal : (graphNegativeCentral S α).Monoidal := by
  unfold graphNegativeCentral; infer_instance
instance graphNegativeCentralAdditive : (graphNegativeCentral S α).Additive := by
  unfold graphNegativeCentral; infer_instance
instance graphNegativeCentralLinear : (graphNegativeCentral S α).Linear ℂ := by
  unfold graphNegativeCentral; infer_instance

/-- The actual graph cap gives the actual ordinary comparison between
the underlying functors of the two genuine central lifts. -/
def graphCentralUnderlyingIso :
    graphNegativeCentral S α ⋙ Center.forget _ ≅
      graphPositiveCentral S α ⋙ Center.forget _ :=
  graphOrbitCapOrdinaryIso S α

/-- Genuine positive-negative centralization is preserved by the
genuine reversed-braided Morita lift. No fullness is used. -/
theorem graphCentral_cross (X Y : D) :
    Centralizes ((graphPositiveCentral S α).obj X)
      ((graphNegativeCentral S α).obj Y) := by
  let K := rightCentralLift D (GraphLagrangian.ModuleOrbit S α)
  have h : @Centralizes (Center D) _ _ (reverseBraiding (Center D))
      ((Drinfeld.positive D).obj X) ((Drinfeld.negative D).obj (α.obj Y)) :=
    (RelativeTensor.centralizes_reverse_iff _ _).mpr
      (Drinfeld.positive_centralizes_negative X (α.obj Y))
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI : K.Braided := rightCentralLiftReverseBraided D (GraphLagrangian.ModuleOrbit S α)
  exact h.map K

end Paper18.Category.GraphPicard
