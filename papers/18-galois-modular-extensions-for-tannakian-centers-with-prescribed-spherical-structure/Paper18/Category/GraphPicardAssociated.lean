import Paper18.Category.GraphPicardAssociatedBasic
import Paper18.Category.GraphPicardDDEquivalence

/-! # The exact double-dual correction of the graph's associated action

Write F₊ and F₋ for the actual strong central-sign actions D → End(M).
The actual corrected cap identifies α ⋙ F₋ with DD ⋙ F₊. Consequently
the actual associated action F₊ ⋙ F₋⁻¹ is DD⁻¹ ⋙ α, as a genuine
monoidal natural isomorphism. The inverse convention satisfies
α ⋙ (F₋ ⋙ F₊⁻¹) ≅ DD. No pivotal identification of DD with Id is used.
-/
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
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual central-sign associated autoequivalence, retaining the
specified composition direction. -/
def graphAssociatedEquivalence : D ≌ D :=
  (graphPositiveActionEquivalence S α hD).trans
    (graphNegativeActionEquivalence S α hD).symm

instance graphAssociatedFunctorMonoidal :
    (graphAssociatedEquivalence S α hD).functor.Monoidal := by
  unfold graphAssociatedEquivalence
  infer_instance
instance graphAssociatedInverseMonoidal :
    (graphAssociatedEquivalence S α hD).inverse.Monoidal := by
  unfold graphAssociatedEquivalence
  infer_instance
instance graphAssociatedEquivalenceMonoidal :
    (graphAssociatedEquivalence S α hD).IsMonoidal := by
  unfold graphAssociatedEquivalence
  infer_instance

/-- The original actual graph cap gives exactly this corrected
associated-action relation, including all genuine tensor constraints. -/
def graphAssociatedDoubleDualIso :
    doubleDualFunctor D ⋙ (graphAssociatedEquivalence S α hD).functor ≅ α :=
  (Functor.associator (doubleDualFunctor D)
    (graphPositiveActionEquivalence S α hD).functor
    (graphNegativeActionEquivalence S α hD).inverse).symm ≪≫
  Functor.isoWhiskerRight (graphOrbitCapCorrectedIso S α).symm
    (graphNegativeActionEquivalence S α hD).inverse ≪≫
  Functor.associator α (graphNegativeActionEquivalence S α hD).functor
    (graphNegativeActionEquivalence S α hD).inverse ≪≫
  Functor.isoWhiskerLeft α (graphNegativeActionEquivalence S α hD).unitIso.symm ≪≫
  Functor.rightUnitor α

instance graphAssociatedDoubleDualIsoMonoidal :
    NatTrans.IsMonoidal (graphAssociatedDoubleDualIso S α hD).hom := by
  dsimp only [graphAssociatedDoubleDualIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

/-- Solving the actual corrected relation uses the genuine inverse
of the canonical double-dual tensor equivalence. -/
def graphAssociatedIso :
    (graphAssociatedEquivalence S α hD).functor ≅
      (doubleDualEquivalence D).inverse ⋙ α :=
  (Functor.leftUnitor (graphAssociatedEquivalence S α hD).functor).symm ≪≫
  Functor.isoWhiskerRight (doubleDualEquivalence D).counitIso.symm
    (graphAssociatedEquivalence S α hD).functor ≪≫
  Functor.associator (doubleDualEquivalence D).inverse (doubleDualFunctor D)
    (graphAssociatedEquivalence S α hD).functor ≪≫
  Functor.isoWhiskerLeft (doubleDualEquivalence D).inverse
    (graphAssociatedDoubleDualIso S α hD)

instance graphAssociatedIsoMonoidal :
    NatTrans.IsMonoidal (graphAssociatedIso S α hD).hom := by
  dsimp only [graphAssociatedIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

/-- The inverse composition convention is recorded explicitly, rather
than identifying it with the first convention. -/
def graphInverseAssociatedDoubleDualIso :
    α ⋙ (graphAssociatedEquivalence S α hD).inverse ≅ doubleDualFunctor D :=
  (Functor.associator α (graphNegativeActionEquivalence S α hD).functor
    (graphPositiveActionEquivalence S α hD).inverse).symm ≪≫
  Functor.isoWhiskerRight (graphOrbitCapCorrectedIso S α)
    (graphPositiveActionEquivalence S α hD).inverse ≪≫
  Functor.associator (doubleDualFunctor D)
    (graphPositiveActionEquivalence S α hD).functor
    (graphPositiveActionEquivalence S α hD).inverse ≪≫
  Functor.isoWhiskerLeft (doubleDualFunctor D)
    (graphPositiveActionEquivalence S α hD).unitIso.symm ≪≫
  Functor.rightUnitor (doubleDualFunctor D)

instance graphInverseAssociatedDoubleDualIsoMonoidal :
    NatTrans.IsMonoidal (graphInverseAssociatedDoubleDualIso S α hD).hom := by
  dsimp only [graphInverseAssociatedDoubleDualIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom]
  infer_instance

end Paper18.Category.GraphPicard
