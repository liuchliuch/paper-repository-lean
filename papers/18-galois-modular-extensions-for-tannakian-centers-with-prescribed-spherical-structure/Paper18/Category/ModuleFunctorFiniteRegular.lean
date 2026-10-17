import Paper18.Category.ModuleFunctorFinite
import Paper18.Category.FixedBoundaryModuleGeneralWatts

/-! # Actual bundled Eilenberg--Watts equivalence for the regular module

Evaluation at the actual tensor unit is an actual complex-linear
equivalence from strong module functors out of the regular module to the
target module category. The inverse and both natural isomorphisms are
constructed from the native action and the proved lineator identities.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u v' u'
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ U : M, (MonoidalLeftAction.actionRight C U).Additive]
  [∀ U : M, (MonoidalLeftAction.actionRight C U).Linear ℂ]

/-- The genuine natural transformation induced by an actual target map. -/
def actionTransformation {U V : M} (f : U ⟶ V) :
    MonoidalLeftAction.actionRight C U ⟶ MonoidalLeftAction.actionRight C V where
  app X := X ⊴ₗ f
  naturality {X Y} g := (MonoidalLeftAction.action_exchange g f).symm

instance actionTransformation_moduleNatural {U V : M} (f : U ⟶ V) :
    IsModuleNatural C (actionTransformation (C := C) f) where
  lineator X Y := by
    change (αₗ X Y U).inv ≫ (X ⊗ Y) ⊴ₗ f =
      (X ⊴ₗ Y ⊴ₗ f) ≫ (αₗ X Y V).inv
    rw [MonoidalLeftAction.tensor_actionHomRight]
    simp

/-- The actual action-on-an-object strong module functor. -/
def actionObject (U : M) : Bundled C C M where
  toFunctor := MonoidalLeftAction.actionRight C U
  leftLinear := actionRightLeftLinear (C := C) U
  additive := inferInstance
  linear := inferInstance

/-- The actual inverse to evaluation at the tensor unit. -/
def actionFunctor : M ⥤ Bundled C C M where
  obj := actionObject
  map f := ⟨actionTransformation (C := C) f,
    show IsModuleNatural C (actionTransformation (C := C) f) from inferInstance⟩
  map_id U := by
    apply bundled_hom_ext
    ext X
    exact MonoidalLeftAction.actionHomRight_id X U
  map_comp f g := by
    apply bundled_hom_ext
    ext X
    exact MonoidalLeftAction.actionHomRight_comp X f g

instance actionFunctor_additive : (actionFunctor (C := C) (M := M)).Additive where
  map_add := by
    intro U V f g
    apply bundled_hom_ext
    ext X
    exact (MonoidalLeftAction.actionLeft M X).map_add

instance actionFunctor_linear : (actionFunctor (C := C) (M := M)).Linear ℂ where
  map_smul f r := by
    apply bundled_hom_ext
    ext X
    exact (MonoidalLeftAction.actionLeft M X).map_smul r f

/-- Evaluate an actual strong module functor at the genuine tensor unit. -/
def evaluationUnit : Bundled C C M ⥤ M where
  obj F := F.toFunctor.obj (𝟙_ C)
  map τ := τ.val.app (𝟙_ C)

instance evaluationUnit_additive : (evaluationUnit (C := C) (M := M)).Additive where
  map_add := by intros; rfl

instance evaluationUnit_linear : (evaluationUnit (C := C) (M := M)).Linear ℂ where
  map_smul _ _ := rfl

/-- The proved actual representing isomorphisms assemble in the actual
module-functor category, with actual module naturality. -/
def evaluationUnitActionIso : 𝟭 (Bundled C C M) ≅
    evaluationUnit (C := C) (M := M) ⋙ actionFunctor (C := C) (M := M) :=
  NatIso.ofComponents (fun F => by
    let e := actionRepresentationIso F.toFunctor
    letI : IsModuleNatural C e.hom := actionRepresentationIso_moduleNatural F.toFunctor
    exact isoMk e) (fun τ => by
    apply bundled_hom_ext
    ext X
    exact actionRepresentationIso_natural τ.val X)

/-- The actual action unitor gives the other natural isomorphism. -/
def actionEvaluationUnitIso : actionFunctor (C := C) (M := M) ⋙
    evaluationUnit (C := C) (M := M) ≅ 𝟭 M :=
  NatIso.ofComponents (fun U => λₗ U)
    (fun f => (MonoidalLeftAction.actionUnitIso_hom_naturality f).symm)

/-- A genuine complex-linear equivalence, with no representing-object
existence or fullness field supplied as an assumption. -/
def regularEquivalence : Bundled C C M ≌ M :=
  CategoryTheory.Equivalence.mk (evaluationUnit (C := C) (M := M))
    (actionFunctor (C := C) (M := M)) evaluationUnitActionIso actionEvaluationUnitIso

instance regularEquivalence_functor_additive :
    (regularEquivalence (C := C) (M := M)).functor.Additive := evaluationUnit_additive

instance regularEquivalence_functor_linear :
    (regularEquivalence (C := C) (M := M)).functor.Linear ℂ := evaluationUnit_linear

instance regularEquivalence_inverse_additive :
    (regularEquivalence (C := C) (M := M)).inverse.Additive := actionFunctor_additive

instance regularEquivalence_inverse_linear :
    (regularEquivalence (C := C) (M := M)).inverse.Linear ℂ := actionFunctor_linear

end Paper18.Category.ModuleFunctor
