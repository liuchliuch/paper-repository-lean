import Paper18.Category.FixedBoundaryInvariantBoundary
import Paper18.Category.FixedBoundaryInvariantNatural
import Paper18.Category.FixedBoundaryFreeComparisonBoundary

/-! # Actual specified-boundary comparison in the original category

Finite regular averaging lifts the genuinely invariant free comparison.
Faithfulness reflects naturality and monoidality. Naturality at the actual
boundary free tensorator retains exactly the prescribed alpha.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonObj Obj
universe v u v' u'
namespace Paper18.Category
open FixedBoundary
variable {G : Type} [Group G] [Fintype G]
  {A : Type u} [Category.{v} A] [Preadditive A] [Linear ℂ A]
  [MonoidalCategory A] [BraidedCategory A]
  {N : Type u'} [Category.{v'} N] [Preadditive N] [Linear ℂ N]
  [MonoidalCategory N] [BraidedCategory N]
  [MonoidalPreadditive N] [MonoidalLinear ℂ N]
  [RightRigidCategory N] [Limits.HasCoequalizers N]
  (F0 : FDRep ℂ G ⥤ A) [F0.Braided] [F0.Additive] [F0.Linear ℂ]
  {i : A ⥤ N} [i.Braided] [i.Additive] [i.Linear ℂ]
  (P : BoundaryAutoequivalence i)
local instance descentLiftImageMonObj : MonObj (i.obj (regularAlgebra F0)) :=
  Functor.monObjObj (F := i) (regularAlgebra F0)
local instance descentLiftImageCommMonObj : IsCommMonObj (i.obj (regularAlgebra F0)) :=
  Functor.isCommMonObj_obj
variable (β : P.moduleFunctor (regularAlgebra F0) ≅ 𝟭 (Mod_ N (i.obj (regularAlgebra F0))))
  (hβ : ∀ (g : G) (M : Mod_ N (i.obj (regularAlgebra F0))),
    (β.hom.app ((Mod_.comap (i.map (regularTranslation F0 g))).obj M)).hom =
      (β.hom.app M).hom)

/-- The actual comparison viewed with the strict identity functor on the
right, so faithful reflection can be applied without changing components. -/
def BoundaryAutoequivalence.moduleFreeComparisonToId :
    P.functor ⋙ InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)) ≅
      𝟭 N ⋙ InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)) :=
  P.moduleFreeComparisonNatIso F0 β ≪≫
    (Functor.leftUnitor (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)))).symm

@[simp] theorem BoundaryAutoequivalence.moduleFreeComparisonToId_hom (X : N) :
    (P.moduleFreeComparisonToId F0 β).hom.app X =
      (P.moduleFreeComparisonNatIso F0 β).hom.app X := by
  simp only [BoundaryAutoequivalence.moduleFreeComparisonToId, Iso.trans_hom,
    NatTrans.comp_app, Functor.leftUnitor_inv_app, Category.comp_id]
  change (P.moduleFreeComparisonNatIso F0 β).hom.app X ≫ 𝟙 _ = _
  exact Category.comp_id _

instance BoundaryAutoequivalence.moduleFreeComparisonToIdMonoidal
    [NatTrans.IsMonoidal β.hom] :
    NatTrans.IsMonoidal (P.moduleFreeComparisonToId F0 β).hom := by
  change NatTrans.IsMonoidal ((P.moduleFreeComparisonNatIso F0 β).hom ≫
    (Functor.leftUnitor (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0)))).inv)
  infer_instance

include hβ in
/-- Actual all-module comparison plus genuine regular-action compatibility
lifts to an actual ordinary comparison in the original extension. -/
def BoundaryAutoequivalence.descendedRegularNatIso : P.functor ≅ 𝟭 N :=
  stagedInvariantNatIso F0 i (P.moduleFreeComparisonToId F0 β) (fun X g => by
    rw [show ((P.moduleFreeComparisonToId F0 β).app X).hom =
      (P.moduleFreeComparisonNatIso F0 β).hom.app X from
        P.moduleFreeComparisonToId_hom F0 β X]
    exact P.moduleFreeComparison_invariant F0 β hβ X g)

include hβ in
@[simp] theorem BoundaryAutoequivalence.free_map_descendedRegularNatIso (X : N) :
    InternalModule.freeMap (A := i.obj (regularAlgebra F0))
      ((P.descendedRegularNatIso F0 β hβ).hom.app X) =
        (P.moduleFreeComparisonNatIso F0 β).hom.app X := by
  rw [← P.moduleFreeComparisonToId_hom F0 β X]
  exact stagedInvariantNatIso_map_hom F0 i _ _ X

instance BoundaryAutoequivalence.descendedRegularNatIsoMonoidal
    [NatTrans.IsMonoidal β.hom] :
    NatTrans.IsMonoidal (P.descendedRegularNatIso F0 β hβ).hom := by
  dsimp only [BoundaryAutoequivalence.descendedRegularNatIso]
  infer_instance

include hβ in
/-- The actual lifted comparison has exactly every specified boundary
component, rather than merely an isomorphic restriction. -/
theorem BoundaryAutoequivalence.descendedRegularNatIso_boundary
    (hboundary : ∀ M : Mod_ A (regularAlgebra F0),
      (β.hom.app ((InternalModule.mapModules i).obj M)).hom = P.boundary.hom.app M.X)
    (X : A) :
    (P.descendedRegularNatIso F0 β hβ).hom.app (i.obj X) = P.boundary.hom.app X := by
  letI := stagedRegularFreeFaithful F0 i
  apply (InternalModule.freeFunctor (A := i.obj (regularAlgebra F0))).map_injective
  change InternalModule.freeMap ((P.descendedRegularNatIso F0 β hβ).hom.app (i.obj X)) =
    InternalModule.freeMap (P.boundary.hom.app X)
  rw [P.free_map_descendedRegularNatIso F0 β hβ]
  rw [P.moduleFreeComparisonNatIso_hom F0 β (i.obj X)]
  exact P.moduleFreeIso_boundary (regularAlgebra F0) β hboundary X

include hβ in
/-- Genuine regular-compatible monoidal module comparison with its exact
boundary values gives the original fixed-boundary trivialization. -/
theorem BoundaryAutoequivalence.trivializable_of_regular_module_comparison
    [NatTrans.IsMonoidal β.hom]
    (hboundary : ∀ M : Mod_ A (regularAlgebra F0),
      (β.hom.app ((InternalModule.mapModules i).obj M)).hom = P.boundary.hom.app M.X) :
    P.Trivializable := by
  refine ⟨{ iso := P.descendedRegularNatIso F0 β hβ, boundary := ?_ }⟩
  intro X
  change (P.descendedRegularNatIso F0 β hβ).hom.app (i.obj X) ≫ 𝟙 _ = _
  rw [Category.comp_id]
  exact P.descendedRegularNatIso_boundary F0 β hβ hboundary X

end Paper18.Category
