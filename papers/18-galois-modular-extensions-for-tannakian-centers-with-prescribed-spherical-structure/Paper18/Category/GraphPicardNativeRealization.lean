import Paper18.Category.GraphPicardRealization
import Paper18.Category.GraphPicardNativeAssociatedBraided

/-! # Actual native graph realization of a prescribed braided autoequivalence

The native convention is α₊ followed by the inverse of α₋. Its signs
are opposite to the central-sign convention. The genuine graph input
DD ⋙ β⁻¹ therefore realizes simultaneousMop(β), with actual monoidal
comparison. The underlying module category is a genuinely chosen
nonempty simple orbit, and both alpha equivalences are constructed.
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
  (β : D ≌ D) [β.functor.Braided] [β.functor.Additive] [β.functor.Linear ℂ]
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual module category realizing the specified actual β under
the native α₊ ⋙ α₋⁻¹ convention. -/
abbrev graphNativeRealizingModule :=
  GraphLagrangian.ModuleOrbit S (graphInverseRealizationInput β)

/-- Its actual positive alpha equivalence, with the native composition
order encoded by the genuine target monoidal opposite. -/
def graphNativeRealizingPositiveEquivalence : Dᴹᵒᵖ ≌
    (ModuleAlphaInduction.End Dᴹᵒᵖ (graphNativeRealizingModule S β))ᴹᵒᵖ :=
  graphPositiveMonoidalEquivalenceOfNondegenerate S (graphInverseRealizationInput β) hD

def graphNativeRealizingNegativeEquivalence : Dᴹᵒᵖ ≌
    (ModuleAlphaInduction.End Dᴹᵒᵖ (graphNativeRealizingModule S β))ᴹᵒᵖ :=
  graphNegativeMonoidalEquivalenceOfNondegenerate S (graphInverseRealizationInput β) hD

instance graphNativeRealizingPositiveMonoidal :
    (graphNativeRealizingPositiveEquivalence S β hD).functor.Monoidal :=
  graphPositiveNondegenerateFunctorMonoidal S (graphInverseRealizationInput β) hD
instance graphNativeRealizingNegativeMonoidal :
    (graphNativeRealizingNegativeEquivalence S β hD).functor.Monoidal :=
  graphNegativeNondegenerateFunctorMonoidal S (graphInverseRealizationInput β) hD

/-- The literal native associated equivalence of this actual module
category. It uses the actual positive and negative alpha equivalences. -/
def graphNativeRealizingAssociatedEquivalence : Dᴹᵒᵖ ≌ Dᴹᵒᵖ :=
  graphNativeAssociatedEquivalence S (graphInverseRealizationInput β) hD

instance graphNativeRealizingAssociatedMonoidal :
    (graphNativeRealizingAssociatedEquivalence S β hD).functor.Monoidal :=
  graphNativeAssociatedFunctorMonoidal S (graphInverseRealizationInput β) hD
instance graphNativeRealizingAssociatedBraided :
    (graphNativeRealizingAssociatedEquivalence S β hD).functor.Braided :=
  graphNativeAssociatedFunctorBraided S (graphInverseRealizationInput β) hD

/-- The genuine native associated action is exactly the specified β
after simultaneous monoidal-opposite transport. -/
def graphNativeRealizingAssociatedIso :
    (graphNativeRealizingAssociatedEquivalence S β hD).functor ≅
      simultaneousMop β.functor :=
  graphNativeAssociatedIso S (graphInverseRealizationInput β) hD ≪≫
    simultaneousMopNatIso (graphInverseRealizationIso S β hD)

instance graphNativeRealizingAssociatedIsoMonoidal :
    NatTrans.IsMonoidal (graphNativeRealizingAssociatedIso S β hD).hom := by
  dsimp only [graphNativeRealizingAssociatedIso, Iso.trans_hom]
  infer_instance

end Paper18.Category.GraphPicard
