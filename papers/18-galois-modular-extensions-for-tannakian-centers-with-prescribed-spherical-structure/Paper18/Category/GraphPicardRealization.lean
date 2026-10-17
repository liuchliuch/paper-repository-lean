import Paper18.Category.GraphPicardAssociatedBraided
import Paper18.Category.SphericalizationAction
import Paper18.Category.MonoidalEquivalenceInverseComparison

/-! # Actual graph-input reparameterization by canonical double duality

For the central-sign convention F₊ ⋙ F₋⁻¹, the actual graph input
DD ⋙ β realizes the prescribed actual braided tensor equivalence β.
The inverse convention is treated by the input DD ⋙ β⁻¹. All comparisons
retain actual monoidality; no pivotal trivialization of DD is used.
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
  (β : D ≌ D) [β.functor.Braided] [β.functor.Additive] [β.functor.Linear ℂ]
  (hD : IsNondegenerate (C := D))
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual graph input correcting the derived DD contribution. -/
def graphRealizationInput : D ⥤ D := doubleDualFunctor D ⋙ β.functor

instance graphRealizationInputBraided : (graphRealizationInput β).Braided := by
  unfold graphRealizationInput; infer_instance
instance graphRealizationInputAdditive : (graphRealizationInput β).Additive := by
  unfold graphRealizationInput; infer_instance
instance graphRealizationInputLinear : (graphRealizationInput β).Linear ℂ := by
  unfold graphRealizationInput; infer_instance
instance graphRealizationInputIsEquivalence : (graphRealizationInput β).IsEquivalence := by
  unfold graphRealizationInput; infer_instance

/-- The actual associated equivalence of the genuinely constructed
reparameterized graph orbit. -/
def graphRealizationEquivalence : D ≌ D :=
  graphAssociatedEquivalence S (graphRealizationInput β) hD

instance graphRealizationFunctorMonoidal :
    (graphRealizationEquivalence S β hD).functor.Monoidal :=
  graphAssociatedFunctorMonoidal S (graphRealizationInput β) hD
instance graphRealizationInverseMonoidal :
    (graphRealizationEquivalence S β hD).inverse.Monoidal :=
  graphAssociatedInverseMonoidal S (graphRealizationInput β) hD
instance graphRealizationIsMonoidal :
    (graphRealizationEquivalence S β hD).IsMonoidal :=
  graphAssociatedEquivalenceMonoidal S (graphRealizationInput β) hD
instance graphRealizationFunctorBraided :
    (graphRealizationEquivalence S β hD).functor.Braided :=
  graphAssociatedFunctorBraided S (graphRealizationInput β) hD

/-- Actual graph-module alpha equivalences realize the specified
actual tensor equivalence after the proved DD correction. -/
def graphRealizationIso : (graphRealizationEquivalence S β hD).functor ≅ β.functor :=
  graphAssociatedIso S (graphRealizationInput β) hD ≪≫
  (Functor.associator (doubleDualEquivalence D).inverse (doubleDualFunctor D) β.functor).symm ≪≫
  Functor.isoWhiskerRight (doubleDualEquivalence D).counitIso β.functor ≪≫
  Functor.leftUnitor β.functor

instance graphRealizationIsoMonoidal :
    NatTrans.IsMonoidal (graphRealizationIso S β hD).hom := by
  dsimp only [graphRealizationIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

section InverseConvention

/-- The actual graph input for the native inverse convention. Its
braided tensor structure uses the actual monoidal inverse of β. -/
def graphInverseRealizationInput : D ⥤ D := doubleDualFunctor D ⋙ β.inverse

instance graphInverseRealizationInputBraided : (graphInverseRealizationInput β).Braided := by
  letI : β.inverse.Monoidal := β.inverseMonoidal
  letI : β.inverse.Braided := DiagonalAlgebra.inverseBraided β
  unfold graphInverseRealizationInput
  infer_instance
instance graphInverseRealizationInputAdditive : (graphInverseRealizationInput β).Additive := by
  unfold graphInverseRealizationInput
  infer_instance
instance graphInverseRealizationInputLinear : (graphInverseRealizationInput β).Linear ℂ := by
  unfold graphInverseRealizationInput
  infer_instance
instance graphInverseRealizationInputIsEquivalence :
    (graphInverseRealizationInput β).IsEquivalence := by
  unfold graphInverseRealizationInput
  infer_instance

/-- The genuine associated forward functor for the inverse input is
the actual monoidal inverse of the prescribed β. -/
def graphInverseRealizationForwardIso :
    (graphAssociatedEquivalence S (graphInverseRealizationInput β) hD).functor ≅ β.inverse :=
  graphAssociatedIso S (graphInverseRealizationInput β) hD ≪≫
  (Functor.associator (doubleDualEquivalence D).inverse (doubleDualFunctor D) β.inverse).symm ≪≫
  Functor.isoWhiskerRight (doubleDualEquivalence D).counitIso β.inverse ≪≫
  Functor.leftUnitor β.inverse

def graphInverseRealizationForwardIsoMonoidal :
    letI : β.inverse.Monoidal := β.inverseMonoidal
    NatTrans.IsMonoidal (graphInverseRealizationForwardIso S β hD).hom := by
  letI : β.inverse.Monoidal := β.inverseMonoidal
  dsimp only [graphInverseRealizationForwardIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom]
  infer_instance

/-- The inverse convention uses the genuine inverse tensor equivalence
as the prescribed input before the actual DD correction. -/
def graphInverseRealizationEquivalence : D ≌ D :=
  (graphAssociatedEquivalence S (graphInverseRealizationInput β) hD).symm

instance graphInverseRealizationFunctorMonoidal :
    (graphInverseRealizationEquivalence S β hD).functor.Monoidal :=
  graphAssociatedInverseMonoidal S (graphInverseRealizationInput β) hD

/-- In the inverse convention the prescribed actual β is recovered
from the actual inverse equivalences, with no ordinary-to-monoidal
upgrade of the Drinfeld map. -/
def graphInverseRealizationIso :
    (graphInverseRealizationEquivalence S β hD).functor ≅ β.functor :=
  Iso.isoInverseOfIsoFunctor (G := graphAssociatedEquivalence S (graphInverseRealizationInput β) hD)
    (G' := β.symm) (graphInverseRealizationForwardIso S β hD)

set_option synthInstance.maxSize 4096 in
instance graphInverseRealizationIsoMonoidal :
    NatTrans.IsMonoidal (graphInverseRealizationIso S β hD).hom := by
  letI : β.inverse.Monoidal := β.inverseMonoidal
  letI : β.IsMonoidal := inferInstance
  letI : NatTrans.IsMonoidal (graphInverseRealizationForwardIso S β hD).hom :=
    graphInverseRealizationForwardIsoMonoidal S β hD
  exact isoInverseOfIsoFunctor_isMonoidal
    (graphAssociatedEquivalence S (graphInverseRealizationInput β) hD) β.symm
    (graphInverseRealizationForwardIso S β hD)
end InverseConvention

end Paper18.Category.GraphPicard
