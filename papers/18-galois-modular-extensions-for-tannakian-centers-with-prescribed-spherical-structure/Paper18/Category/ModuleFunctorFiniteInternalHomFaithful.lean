import Paper18.Category.ModuleFunctorFiniteInternalHomBasic
import Paper18.Category.ModuleComponentConnected
import Mathlib.CategoryTheory.Adjunction.FullyFaithful

/-! # Faithfulness of internal Hom on an actual simple action component

The actual simple retract generation of an orbit component detects all
morphisms under the constructed internal Hom functor. Thus the actual
adjunction counit is epimorphic. No generator or indecomposability field
is assumed for the entire module category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w wM
namespace Paper18.Category.ModuleInternalHom
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft M X).Linear ℂ]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Additive]
  [∀ n : M, (MonoidalLeftAction.actionRight C n).Linear ℂ]
  {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ)

/-- Actual simple action retracts make the constructed internal Hom
faithful. The orbit-component specialization below derives these
retracts from the actual action instead of accepting them as a field. -/
def faithfulOfSimpleRetracts (n : M)
    (hgen : ∀ j : κ, ∃ X : C, Nonempty (Retract (SM.simpleObject j) (X ⊙ₗ n))) :
    (internalHomFunctor S n).toFunctor.Faithful where
  map_injective {m m'} f g h := by
    apply SM.hom_ext_simples
    intro j b
    obtain ⟨X, ⟨r⟩⟩ := hgen j
    have ha : (r.r ≫ b) ≫ f = (r.r ≫ b) ≫ g := by
      apply ((adjunction S n).homEquiv X m').injective
      simp only [Adjunction.homEquiv_naturality_right, Functor.map_comp, Category.assoc]
      rw [h]
    have hb := congrArg (fun z => r.i ≫ z) ha
    simpa only [← Category.assoc, r.retract, Category.id_comp] using hb

instance componentActionRight_additive (i : κ) (n : ModuleComponent.Component (C := C) SM i) :
    (MonoidalLeftAction.actionRight C n).Additive where
  map_add := (MonoidalLeftAction.actionRight C n.obj).map_add

instance componentActionRight_linear (i : κ) (n : ModuleComponent.Component (C := C) SM i) :
    (MonoidalLeftAction.actionRight C n).Linear ℂ where
  map_smul f r := (MonoidalLeftAction.actionRight C n.obj).map_smul r f

/-- The constructed internal Hom based at the actual generating simple
of one genuine action component is faithful. -/
def componentInternalHomFaithful (i : κ) :
    (internalHomFunctor S (ModuleComponent.base (C := C) SM i)).toFunctor.Faithful := by
  letI : HasKernels (ModuleComponent.Component (C := C) SM i) := ModuleComponent.hasKernels SM i
  exact faithfulOfSimpleRetracts S (ModuleComponent.skeleton (C := C) SM i)
    (ModuleComponent.base (C := C) SM i) (ModuleComponent.simple_retract_action_base SM i)

/-- Every actual evaluation map in the genuine orbit component is
an epimorphism, as a consequence of the proved faithfulness. -/
def componentEvaluationEpi (i : κ) (m : ModuleComponent.Component (C := C) SM i) :
    Epi (evaluation S (ModuleComponent.base (C := C) SM i) m) := by
  letI := componentInternalHomFaithful S SM i
  exact (adjunction S (ModuleComponent.base (C := C) SM i)).counit_epi_of_R_faithful m

end Paper18.Category.ModuleInternalHom
