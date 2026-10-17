import Paper18.Category.GraphPicardGeneratorNaturality
import Paper18.Category.GraphPicardCentralCharacter
import Paper18.Category.GraphPicardCapTranspose

/-! # The actual natural comparison obtained from the graph cap

Every component is the genuine rigid transpose of the graph algebra's
actual cap followed by its actual action on internal modules. Naturality
is derived from the cap's genuine dinaturality, rather than supplied as
comparison data.
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
attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
local notation "A" => GraphLagrangian.algebra S α
local instance graphCapUnderlyingMonObj : MonObj A.1 :=
  Functor.monObjObj (F := Center.forget D) A
local notation "H" => rightCentralAction D (Mod_ D A.1)

/-- Actual positive central action on the actual graph module category. -/
def graphCapPositive : D ⥤ ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1) :=
  Drinfeld.positive D ⋙ H

/-- Actual negative central action, after the specified actual braided
self-equivalence, on the actual graph module category. -/
def graphCapNegative : D ⥤ ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1) :=
  α ⋙ Drinfeld.negative D ⋙ H

instance graphCapPositiveMonoidal : (graphCapPositive S α).Monoidal := by
  unfold graphCapPositive
  infer_instance
instance graphCapNegativeMonoidal : (graphCapNegative S α).Monoidal := by
  unfold graphCapNegative
  infer_instance

/-- The genuine graph cap acts by a genuine module-natural pairing. -/
def graphCapPairing (X : D) :
    (graphCapPositive S α).obj (dual D X) ⊗ (graphCapNegative S α).obj X ⟶
      𝟙_ (ModuleAlphaInduction.End Dᴹᵒᵖ (Mod_ D A.1)) :=
  Functor.LaxMonoidal.μ H ((Drinfeld.positive D).obj (dual D X))
      ((Drinfeld.negative D).obj (α.obj X)) ≫ centralCapHom A (graphCap S α X)

/-- The actual endofunctor-valued graph pairing is dinatural. -/
lemma graphCapPairing_dinaturality {X Y : D} (f : X ⟶ Y) :
    (graphCapPositive S α).map (dualMap D f) ▷ (graphCapNegative S α).obj X ≫
        graphCapPairing S α X =
      (graphCapPositive S α).obj (dual D Y) ◁ (graphCapNegative S α).map f ≫
        graphCapPairing S α Y := by
  dsimp only [graphCapPairing, centralCapHom, graphCapPositive, graphCapNegative,
    Functor.comp_map, Functor.comp_obj]
  rw [Functor.LaxMonoidal.μ_natural_left_assoc,
    Functor.LaxMonoidal.μ_natural_right_assoc,
    ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
  have hd := graphCap_dinaturality S α f
  simp only [MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom] at hd
  rw [hd]

/-- The actual graph cap yields a genuine natural transformation between
its two genuine alpha-type module functors. -/
def graphCapComparison : graphCapNegative S α ⟶ graphCapPositive S α :=
  capFamilyNatTrans (graphCapPositive S α) (graphCapNegative S α)
    (graphCapPairing S α) (graphCapPairing_dinaturality S α)

/-- The comparison is characterized by the genuine transported cap
identity; no component or invertibility conclusion is assumed. -/
@[reassoc] lemma graphCapComparison_evaluation (X : D) :
    (graphCapPositive S α).obj (dual D X) ◁ (graphCapComparison S α).app X ≫
      @ExactPairing.evaluation _ _ _ ((graphCapPositive S α).obj X)
        ((graphCapPositive S α).obj (dual D X))
        (mapExactPairing (graphCapPositive S α) X (dual D X)) =
      graphCapPairing S α X :=
  capFamilyNatTrans_evaluation _ _ _ _ X

end Paper18.Category.GraphPicard
