import Paper18.Category.GraphPicardAssociated

/-! # The actual associated autoequivalence is braided and complex linear -/
noncomputable section
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

instance graphPositiveActionFunctorAdditive :
    (graphPositiveActionEquivalence S α hD).functor.Additive :=
  inferInstanceAs (graphPositiveOrbitAction S α).Additive
instance graphNegativeActionFunctorAdditive :
    (graphNegativeActionEquivalence S α hD).functor.Additive :=
  inferInstanceAs (graphNegativeOrbitAction S α).Additive
instance graphPositiveActionFunctorLinear :
    (graphPositiveActionEquivalence S α hD).functor.Linear ℂ :=
  inferInstanceAs ((graphPositiveOrbitAction S α).Linear ℂ)
instance graphNegativeActionFunctorLinear :
    (graphNegativeActionEquivalence S α hD).functor.Linear ℂ :=
  inferInstanceAs ((graphNegativeOrbitAction S α).Linear ℂ)

instance graphAssociatedFunctorAdditive :
    (graphAssociatedEquivalence S α hD).functor.Additive := by
  change ((graphPositiveActionEquivalence S α hD).functor ⋙
    (graphNegativeActionEquivalence S α hD).inverse).Additive
  infer_instance
instance graphAssociatedFunctorLinear :
    (graphAssociatedEquivalence S α hD).functor.Linear ℂ := by
  change ((graphPositiveActionEquivalence S α hD).functor ⋙
    (graphNegativeActionEquivalence S α hD).inverse).Linear ℂ
  infer_instance

/-- Braidedness is transported along the actual monoidal DD-corrected
comparison, rather than along the nonmonoidal Drinfeld map. -/
instance graphAssociatedFunctorBraided :
    (graphAssociatedEquivalence S α hD).functor.Braided where
  braided X Y := by
    let e := graphAssociatedIso S α hD
    letI : NatTrans.IsMonoidal e.symm.hom :=
      inferInstanceAs (NatTrans.IsMonoidal e.inv)
    letI : (graphAssociatedEquivalence S α hD).functor.LaxMonoidal :=
      (graphAssociatedFunctorMonoidal S α hD).toLaxMonoidal
    let hb := Functor.LaxBraided.ofNatIso e.symm
    exact hb.braided X Y

instance graphAssociatedInverseBraided :
    (graphAssociatedEquivalence S α hD).inverse.Braided where
  braided X Y := by
    let e := graphAssociatedEquivalence S α hD
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
