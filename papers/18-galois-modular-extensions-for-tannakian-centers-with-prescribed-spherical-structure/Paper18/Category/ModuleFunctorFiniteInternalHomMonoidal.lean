import Paper18.Category.ModuleFunctorFiniteRegular
import Paper18.Category.ModuleAlphaInductionEnd
import Mathlib.CategoryTheory.Monoidal.Mon_

/-! # The actual monoidal regular-module Eilenberg--Watts equivalence

Right tensoring is genuinely strong monoidal into actual strong module
endofunctors. Its inverse, evaluation at the actual unit, inherits the
actual strong monoidal structure. This transfers actual monads to actual
internal algebras without assuming algebra laws.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open scoped MonoidalLeftAction
universe v u
namespace Paper18.Category.ModuleInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]

instance regularActionLeft_additive (X : C) :
    (MonoidalLeftAction.actionLeft C X).Additive where
  map_add := by
    intro U V f g
    change X ◁ (f + g) = _
    exact (tensorLeft X).map_add

instance regularActionLeft_linear (X : C) :
    (MonoidalLeftAction.actionLeft C X).Linear ℂ where
  map_smul f r := by
    change X ◁ (r • f) = _
    exact (tensorLeft X).map_smul r f

instance regularActionRight_additive (X : C) :
    (MonoidalLeftAction.actionRight C X).Additive where
  map_add := by
    intro U V f g
    change (f + g) ▷ X = _
    exact (tensorRight X).map_add

instance regularActionRight_linear (X : C) :
    (MonoidalLeftAction.actionRight C X).Linear ℂ where
  map_smul f r := by
    change (r • f) ▷ X = _
    exact (tensorRight X).map_smul r f

/-- The actual associator is an actual module natural tensor comparison. -/
def regularTensorIso (U V : C) :
    ModuleFunctor.actionObject (C := C) U ⊗ ModuleFunctor.actionObject (C := C) V ≅
      ModuleFunctor.actionObject (C := C) (U ⊗ V) := by
  let e := (tensorRightTensor U V).symm
  letI : ModuleFunctor.IsModuleNatural C e.hom := {
    lineator X m := by
      change ((α_ X (m ⊗ U) V).inv ≫ (α_ X m U).inv ▷ V) ≫ (α_ (X ⊗ m) U V).hom =
        X ◁ (α_ m U V).hom ≫ (α_ X m (U ⊗ V)).inv
      monoidal }
  exact ModuleFunctor.isoMk e

/-- The actual right unitor gives the actual unit comparison. -/
def regularUnitIso :
    𝟙_ (ModuleAlphaInduction.End C C) ≅ ModuleFunctor.actionObject (C := C) (𝟙_ C) := by
  let e := (rightUnitorNatIso C).symm
  letI : ModuleFunctor.IsModuleNatural C e.hom := {
    lineator X m := by
      change 𝟙 _ ≫ (ρ_ (X ⊗ m)).inv = X ◁ (ρ_ m).inv ≫ (α_ X m (𝟙_ C)).inv
      monoidal }
  exact ModuleFunctor.isoMk e

/-- Right tensoring is genuinely strong monoidal in the composition
convention of the actual module-endofunctor category. -/
instance regularActionMonoidal : (ModuleFunctor.actionFunctor (C := C) (M := C)).Monoidal :=
  Functor.CoreMonoidal.toMonoidal {
    εIso := regularUnitIso (C := C)
    μIso U V := regularTensorIso U V
    μIso_hom_natural_left {U U'} f V := by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      change ((m ◁ f) ▷ V) ≫ (α_ m U' V).hom =
        (α_ m U V).hom ≫ m ◁ (f ▷ V)
      monoidal
    μIso_hom_natural_right {V V'} U f := by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      change ((m ⊗ U) ◁ f) ≫ (α_ m U V').hom =
        (α_ m U V).hom ≫ m ◁ (U ◁ f)
      monoidal
    associativity U V W := by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      change (α_ m U V).hom ▷ W ≫ (α_ m (U ⊗ V) W).hom ≫ m ◁ (α_ U V W).hom =
        𝟙 _ ≫ (α_ (m ⊗ U) V W).hom ≫ (α_ m U (V ⊗ W)).hom
      monoidal
    left_unitality U := by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      change 𝟙 _ = (ρ_ m).inv ▷ U ≫ (α_ m (𝟙_ C) U).hom ≫ m ◁ (λ_ U).hom
      monoidal
    right_unitality U := by
      apply ModuleFunctor.bundled_hom_ext
      ext m
      change 𝟙 _ = (ρ_ (m ⊗ U)).inv ≫ (α_ m U (𝟙_ C)).hom ≫ m ◁ (ρ_ U).hom
      monoidal }

/-- Evaluation at the unit is genuinely strong monoidal, as the actual
inverse of the constructed regular-module equivalence. -/
instance regularEvaluationMonoidal : (ModuleFunctor.evaluationUnit (C := C) (M := C)).Monoidal := by
  let e := ModuleFunctor.regularEquivalence (C := C) (M := C)
  letI : e.symm.functor.Monoidal :=
    inferInstanceAs ((ModuleFunctor.actionFunctor (C := C) (M := C)).Monoidal)
  exact e.symm.inverseMonoidal

end Paper18.Category.ModuleInternalHom
