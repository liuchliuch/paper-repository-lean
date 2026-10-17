import Paper18.Category.GraphPicardNativeAssociated
import Paper18.Category.GraphPicardNativeMonoidalBraided

/-! # Actual braided linear structures of the native associated action -/
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

instance graphNativePositiveFunctorAdditive :
    (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).functor.Additive :=
  inferInstanceAs (graphPositiveMop S α).Additive
instance graphNativeNegativeFunctorAdditive :
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).functor.Additive :=
  inferInstanceAs (graphNegativeMop S α).Additive
instance graphNativePositiveFunctorLinear :
    (graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).functor.Linear ℂ :=
  inferInstanceAs ((graphPositiveMop S α).Linear ℂ)
instance graphNativeNegativeFunctorLinear :
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).functor.Linear ℂ :=
  inferInstanceAs ((graphNegativeMop S α).Linear ℂ)

instance graphNativeAssociatedFunctorAdditive :
    (graphNativeAssociatedEquivalence S α hD).functor.Additive := by
  change ((graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).functor ⋙
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).inverse).Additive
  infer_instance
instance graphNativeAssociatedFunctorLinear :
    (graphNativeAssociatedEquivalence S α hD).functor.Linear ℂ := by
  change ((graphPositiveMonoidalEquivalenceOfNondegenerate S α hD).functor ⋙
    (graphNegativeMonoidalEquivalenceOfNondegenerate S α hD).inverse).Linear ℂ
  infer_instance

/-- The exact monoidal sign comparison transports the already proved
actual braidedness of the inverse central associated autoequivalence. -/
instance graphNativeAssociatedFunctorBraided :
    (graphNativeAssociatedEquivalence S α hD).functor.Braided where
  braided X Y := by
    let e := graphNativeAssociatedIso S α hD
    letI : NatTrans.IsMonoidal e.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal e.inv)
    letI : (graphNativeAssociatedEquivalence S α hD).functor.LaxMonoidal :=
      (graphNativeAssociatedFunctorMonoidal S α hD).toLaxMonoidal
    let hb := Functor.LaxBraided.ofNatIso e.symm
    exact hb.braided X Y

/-- The inverse equivalence is braided for its genuine transported
tensor structure, by faithful cancellation through the forward functor. -/
instance graphNativeAssociatedInverseBraided :
    (graphNativeAssociatedEquivalence S α hD).inverse.Braided where
  braided X Y := by
    let e := graphNativeAssociatedEquivalence S α hD
    letI : NatTrans.IsMonoidal e.counitIso.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal e.counitIso.inv)
    letI : (e.inverse ⋙ e.functor).LaxBraided := Functor.LaxBraided.ofNatIso e.counitIso.symm
    have h := Functor.LaxBraided.braided (F := e.inverse ⋙ e.functor) X Y
    apply e.functor.map_injective
    apply (cancel_epi (Functor.LaxMonoidal.μ e.functor (e.inverse.obj X) (e.inverse.obj Y))).mp
    simp only [Functor.map_comp]
    rw [Functor.LaxBraided.braided_assoc]
    simpa only [Functor.comp_map, Functor.comp_obj, Functor.LaxMonoidal.comp_μ,
      Category.assoc] using h

end Paper18.Category.GraphPicard
