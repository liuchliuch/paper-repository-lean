import Paper18.Category.GraphPicardComparisonDefect
import Paper18.Category.GraphPicardComponentCap
import Paper18.Category.GraphPicardNativeComparison
import Paper18.Category.MonoidalNatTransRigid

/-! # The actual corrected graph comparison and its genuine inverse

The double-dual correction satisfies the actual unit and tensor laws.
Its inverse is constructed by rigidity, and both maps restrict to the
actual nonempty graph orbit.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits Functor.LaxMonoidal MonoidalOpposite
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

/-- The corrected comparison has the actual cup-cap inverse supplied
by rigidity of the source. No rigidity of the whole module End category
or pivotal structure is used. -/
def graphCapCorrectedIso : graphCapNegative S α ≅
    doubleDualFunctor D ⋙ graphCapPositive S α :=
  monoidalNatTransIso (graphCapCorrectedComparison S α)

@[simp] lemma graphCapCorrectedIso_hom :
    (graphCapCorrectedIso S α).hom = graphCapCorrectedComparison S α := rfl

instance graphCapCorrectedIsoMonoidal :
    NatTrans.IsMonoidal (graphCapCorrectedIso S α).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (graphCapCorrectedComparison S α))

/-- Both the actual corrected transformation and its actual rigid
inverse preserve the genuine graph orbit. -/
def graphOrbitCapCorrectedIso :
    α ⋙ Drinfeld.negative D ⋙ rightCentralAction D (GraphLagrangian.ModuleOrbit S α) ≅
      doubleDualFunctor D ⋙ Drinfeld.positive D ⋙
        rightCentralAction D (GraphLagrangian.ModuleOrbit S α) :=
  NatIso.ofComponents (fun X =>
    componentCentralIso (GraphLagrangian.moduleSkeleton S α)
      ((GraphLagrangian.underlyingSeparableNoPivotal S α).orbitLabel S
        (GraphLagrangian.underlying_id_ne_zero S α))
      ((graphCapCorrectedIso S α).app X))
    (fun {X Y} f => by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      exact congrArg (fun q => q.val.app m.obj)
        ((graphCapCorrectedIso S α).hom.naturality f))

/-- The actual restricted inverse comparison retains the actual strong
tensor coherence; the equations are reflected by the full inclusion of
the actual orbit component. -/
instance graphOrbitCapCorrectedIsoMonoidal :
    NatTrans.IsMonoidal (graphOrbitCapCorrectedIso S α).hom where
  unit := by
    apply ModuleFunctor.bundled_hom_ext
    ext m
    exact congrArg (fun q => q.val.app m.obj)
      (NatTrans.IsMonoidal.unit (τ := (graphCapCorrectedIso S α).hom))
  tensor X Y := by
    apply ModuleFunctor.bundled_hom_ext
    ext m
    exact congrArg (fun q => q.val.app m.obj)
      (NatTrans.IsMonoidal.tensor (τ := (graphCapCorrectedIso S α).hom) X Y)

end Paper18.Category.GraphPicard
