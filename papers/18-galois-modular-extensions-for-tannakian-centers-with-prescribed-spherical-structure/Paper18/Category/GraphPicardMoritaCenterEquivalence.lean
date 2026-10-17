import Paper18.Category.GraphPicardMoritaCenterEquivalenceBasic

/-! # The actual graph Morita central lift is an equivalence

The original central lift is genuinely fully faithful. The actual source
and constructed target center skeletons have equal intrinsic FP dimension,
so actual simple images exhaust the target and actual biproducts give
essential surjectivity. Its actual source braiding is reversed, as dictated
by native endofunctor composition. No desired equivalence or dominance law
is supplied as data.
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
attribute [local instance] moritaCenterEndKernels moritaCenterEndFiniteHom
  moritaCenterEndRightRigid moritaCenterEndSimpleUnit moritaCenterEndLeftRigid moritaCenterFiniteHom

/-- Actual fullness of the original Morita center lift, derived before
any center-equivalence conclusion. -/
instance graphMoritaCenterLiftFull :
    (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).Full :=
  (graphCentralLiftFullyFaithful S α).full

/-- Actual faithfulness of that same original Morita center lift. -/
instance graphMoritaCenterLiftFaithful :
    (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).Faithful :=
  (graphCentralLiftFullyFaithful S α).faithful

/-- Equal actual total center dimensions and actual full faithfulness
construct essential surjectivity of the original central lift. -/
def graphMoritaCenterLiftEssSurj :
    (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).EssSurj :=
  (DrinfeldCoendModules.centerSkeletonNoPivotal S).essSurjOfTotalFPdimEq
    (graphMoritaCenterSkeleton S α hD)
    (rightCentralLift D (GraphLagrangian.ModuleOrbit S α))
    (graphMoritaCenter_totalFPdim_eq S α hD)

/-- The actual original Morita central lift is an actual equivalence. -/
def graphMoritaCenterLiftIsEquivalence :
    (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).IsEquivalence where
  faithful := inferInstance
  full := inferInstance
  essSurj := graphMoritaCenterLiftEssSurj S α hD

/-- The genuine graph Morita center equivalence retains exactly the
original rightCentralLift as its actual forward functor. -/
def graphMoritaCenterEquivalence : Center D ≌
    Center (ModuleAlphaInduction.End Dᴹᵒᵖ (GraphLagrangian.ModuleOrbit S α)) := by
  letI := graphMoritaCenterLiftIsEquivalence S α hD
  exact (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).asEquivalence

instance graphMoritaCenterEquivalenceFunctorMonoidal :
    (graphMoritaCenterEquivalence S α hD).functor.Monoidal :=
  inferInstanceAs (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).Monoidal
instance graphMoritaCenterEquivalenceFunctorAdditive :
    (graphMoritaCenterEquivalence S α hD).functor.Additive :=
  inferInstanceAs (rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).Additive
instance graphMoritaCenterEquivalenceFunctorLinear :
    (graphMoritaCenterEquivalence S α hD).functor.Linear ℂ :=
  inferInstanceAs ((rightCentralLift D (GraphLagrangian.ModuleOrbit S α)).Linear ℂ)
instance graphMoritaCenterEquivalenceInverseMonoidal :
    (graphMoritaCenterEquivalence S α hD).inverse.Monoidal :=
  (graphMoritaCenterEquivalence S α hD).inverseMonoidal
instance graphMoritaCenterEquivalenceIsMonoidal :
    (graphMoritaCenterEquivalence S α hD).IsMonoidal := by
  infer_instance

/-- The actual graph Morita equivalence preserves the reversed source
center braiding and the canonical target center braiding. -/
def graphMoritaCenterEquivalenceReverseBraided :
    letI : BraidedCategory (Center D) := reverseBraiding (Center D)
    (graphMoritaCenterEquivalence S α hD).functor.Braided :=
  rightCentralLiftReverseBraided D (GraphLagrangian.ModuleOrbit S α)

/-- The actual inverse is braided with respect to exactly those same
source and target braidings, by faithful cancellation. -/
def graphMoritaCenterEquivalenceInverseReverseBraided :
    letI : BraidedCategory (Center D) := reverseBraiding (Center D)
    (graphMoritaCenterEquivalence S α hD).inverse.Braided := by
  letI : BraidedCategory (Center D) := reverseBraiding (Center D)
  letI := graphMoritaCenterEquivalenceReverseBraided S α hD
  let e := graphMoritaCenterEquivalence S α hD
  refine { braided := ?_ }
  intro X Y
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
