import Paper18.Category.ModuleAlphaInductionEquivalenceBasic
import Paper18.Category.ModuleFunctorAdjointNaturality

/-! # Actual invertibility of module autoequivalences and their representers

The inverse strong module structure is the actual adjoint mate structure.
The actual unit and counit are module-natural, giving genuine tensor inverse
data in the endofunctor category.  No representing or inverse object is
supplied as a conclusion field.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open MonoidalOpposite
universe v u vM uM
namespace Paper18.Category.ModuleAlphaInduction
variable (C : Type u) [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  (M : Type uM) [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  (F : End C M) [F.toFunctor.IsEquivalence]

/-- The actual quasi-inverse of a strong module autoequivalence, with its
derived strong module lineator and inherited additivity and linearity. -/
def inverseEnd : End C M where
  toFunctor := F.toFunctor.asEquivalence.inverse
  leftLinear := ModuleFunctor.rightAdjointLeftLinear (C := C) F.toFunctor
    F.toFunctor.asEquivalence.toAdjunction
  additive := by
    letI : F.toFunctor.asEquivalence.functor.Additive := inferInstanceAs F.toFunctor.Additive
    exact CategoryTheory.Equivalence.inverse_additive _
  linear := by
    letI : F.toFunctor.asEquivalence.functor.Linear ℂ := inferInstanceAs (Functor.Linear ℂ F.toFunctor)
    exact CategoryTheory.Equivalence.inverseLinear ℂ _

/-- The ordinary counit is an actual morphism of strong module functors. -/
def inverseEnd_counit_moduleNatural :
    letI : F.toFunctor.asEquivalence.functor.LeftLinear C := F.leftLinear
    letI : F.toFunctor.asEquivalence.inverse.LeftLinear C := (inverseEnd C M F).leftLinear
    ModuleFunctor.IsModuleNatural C F.toFunctor.asEquivalence.counitIso.hom :=
  ModuleFunctor.rightAdjointCounit_moduleNatural (C := C) F.toFunctor
    F.toFunctor.asEquivalence.toAdjunction

/-- The ordinary unit is an actual morphism of strong module functors. -/
def inverseEnd_unit_moduleNatural :
    letI : F.toFunctor.asEquivalence.functor.LeftLinear C := F.leftLinear
    letI : F.toFunctor.asEquivalence.inverse.LeftLinear C := (inverseEnd C M F).leftLinear
    ModuleFunctor.IsModuleNatural C F.toFunctor.asEquivalence.unitIso.hom :=
  ModuleFunctor.rightAdjointUnit_moduleNatural (C := C) F.toFunctor
    F.toFunctor.asEquivalence.toAdjunction

/-- An actual module autoequivalence is an actual invertible object of the
composition monoidal category of strong module endofunctors. -/
def endTensorInverse : TensorInverse F := by
  letI : F.toFunctor.asEquivalence.functor.LeftLinear C := F.leftLinear
  letI : F.toFunctor.asEquivalence.inverse.LeftLinear C := (inverseEnd C M F).leftLinear
  letI : ModuleFunctor.IsModuleNatural C F.toFunctor.asEquivalence.counitIso.hom :=
    inverseEnd_counit_moduleNatural C M F
  letI : ModuleFunctor.IsModuleNatural C F.toFunctor.asEquivalence.unitIso.hom :=
    inverseEnd_unit_moduleNatural C M F
  exact
    { inverse := inverseEnd C M F
      left := ModuleFunctor.isoMk F.toFunctor.asEquivalence.counitIso
      right := (ModuleFunctor.isoMk F.toFunctor.asEquivalence.unitIso).symm }

variable [BraidedCategory C] [(negative C M).IsEquivalence]

/-- An actual module autoequivalence has an actual tensor-invertible
neutral representing object, constructed through strong alpha induction. -/
def negativeAutoequivalenceTensorInverse :
    TensorInverse (negativeRepresentingObject C M F) :=
  negativeRepresenterTensorInverse C M F (endTensorInverse C M F)

/-- The representing object, its genuine two-sided inverse, and its actual
module-natural representing isomorphism are all derived. -/
theorem exists_invertible_negative_representer :
    ∃ Z : C, Nonempty (TensorInverse Z) ∧ Nonempty ((negative C M).obj Z ≅ F) :=
  ⟨negativeRepresentingObject C M F, ⟨negativeAutoequivalenceTensorInverse C M F⟩,
    ⟨negativeRepresentationIso C M F⟩⟩

end Paper18.Category.ModuleAlphaInduction
