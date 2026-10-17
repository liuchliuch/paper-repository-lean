import Paper18.Category.GraphPicardNativeAssociatedBasic
import Paper18.Category.GraphPicardAssociatedBraided

/-! # The genuine associated action of native graph alpha induction

The native convention is alpha-plus followed by the inverse of alpha-minus.
The two native signs correspond to opposite central signs, so its actual
monoidal functor is the simultaneous monoidal opposite of the *inverse*
central-sign associated autoequivalence. The comparison uses only the actual
monoidal sign adapters and genuine equivalence unit and counit.
-/
noncomputable section
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

instance nativeAssociatedPositiveInverse :
    (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).inverse.Monoidal :=
  graphPositiveNondegenerateInverseMonoidal S α hD
instance nativeAssociatedNegativeInverse :
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).inverse.Monoidal :=
  graphNegativeNondegenerateInverseMonoidal S α hD
instance nativeAssociatedPositiveEquivalence :
    (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).IsMonoidal :=
  graphPositiveNondegenerateEquivalenceIsMonoidal S α hD
instance nativeAssociatedNegativeEquivalence :
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).IsMonoidal :=
  graphNegativeNondegenerateEquivalenceIsMonoidal S α hD

/-- The actual native graph associated equivalence has the literal
alpha-plus then inverse-alpha-minus composition direction. -/
def graphNativeAssociatedEquivalence : Dᴹᵒᵖ ≌ Dᴹᵒᵖ :=
  (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).trans
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).symm

instance graphNativeAssociatedFunctorMonoidal :
    (graphNativeAssociatedEquivalence S α hD).functor.Monoidal := by
  unfold graphNativeAssociatedEquivalence
  infer_instance
instance graphNativeAssociatedInverseMonoidal :
    (graphNativeAssociatedEquivalence S α hD).inverse.Monoidal := by
  unfold graphNativeAssociatedEquivalence
  infer_instance
instance graphNativeAssociatedEquivalenceMonoidal :
    (graphNativeAssociatedEquivalence S α hD).IsMonoidal := by
  unfold graphNativeAssociatedEquivalence
  infer_instance

/-- The inverse native-negative equivalence is compared with the actual
simultaneous opposite of the inverse positive central action. -/
def graphNativeNegativeInverseIso :
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).inverse ≅
      simultaneousMop (graphPositiveActionEquivalence S α hD).inverse :=
  inverseMopComparison (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD)
    (graphPositiveActionEquivalence S α hD)
    (nativeNegativeMonoidalIso D (GraphLagrangian.ModuleOrbit S α))

instance graphNativeNegativeInverseIsoMonoidal :
    NatTrans.IsMonoidal (graphNativeNegativeInverseIso S α hD).hom := by
  dsimp only [graphNativeNegativeInverseIso]
  infer_instance

/-- The precise native-sign comparison is monoidal and reverses the
central associated equivalence. No ordinary Drinfeld isomorphism is
asserted to be monoidal. -/
def graphNativeAssociatedIso :
    (graphNativeAssociatedEquivalence S α hD).functor ≅
      simultaneousMop (graphAssociatedEquivalence S α hD).inverse :=
  Functor.isoWhiskerRight (nativePositiveMonoidalIso D (GraphLagrangian.ModuleOrbit S α))
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).inverse ≪≫
  Functor.isoWhiskerLeft (simultaneousMop (graphNegativeActionEquivalence S α hD).functor)
    (graphNativeNegativeInverseIso S α hD) ≪≫
  (simultaneousMopCompIso (graphNegativeActionEquivalence S α hD).functor
    (graphPositiveActionEquivalence S α hD).inverse).symm

instance graphNativeAssociatedIsoMonoidal :
    NatTrans.IsMonoidal (graphNativeAssociatedIso S α hD).hom := by
  dsimp only [graphNativeAssociatedIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom]
  infer_instance

end Paper18.Category.GraphPicard
