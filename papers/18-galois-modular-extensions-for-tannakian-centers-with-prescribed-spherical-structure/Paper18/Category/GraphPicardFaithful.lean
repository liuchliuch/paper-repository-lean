import Paper18.Category.GraphPicardContraction
import Paper18.Category.InternalModuleAmbientActionLinear
import Paper18.Category.ModuleComponentAction
import Paper18.Category.ModuleAlphaInductionFunctor
import Paper18.Category.SeparableModulesSemisimple

/-! # Actual faithfulness of alpha induction on internal-module components -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonObj MonoidalLeftAction
universe v u w wM
namespace Paper18.Category.GraphPicard
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D] [Simple (𝟙_ D)]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)
  {R : D} [MonObj R]

/-- A genuine simple internal module has a nonzero actual underlying object. -/
lemma simpleModule_underlying_nonzero (M : Mod_ D R) [Simple M] : 𝟙 M.X ≠ 0 := by
  intro h
  apply CategoryTheory.id_nonzero M
  apply Mod_.Hom.ext
  exact h

attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction
variable {κ : Type wM} [Fintype κ] (SM : FiniteSemisimpleSkeleton (Mod_ D R) κ) (i : κ)

/-- Evaluation of the actual ambient action on the actual base module of
a component is faithful. No invertibility of that component is assumed. -/
def componentActionRightFaithful :
    (MonoidalLeftAction.actionRight Dᴹᵒᵖ
      (ModuleComponent.base (C := Dᴹᵒᵖ) SM i)).Faithful where
  map_injective {X Y} f g h := by
    let n := ModuleComponent.base (C := Dᴹᵒᵖ) SM i
    have hh := congrArg Mod_.Hom.hom h
    change n.obj.X ◁ f.unmop = n.obj.X ◁ g.unmop at hh
    letI : Simple n.obj := SM.simple i
    letI := tensorLeftFaithfulOfNonzero S n.obj.X (simpleModule_underlying_nonzero n.obj)
    apply Quiver.Hom.unmop_inj
    exact (tensorLeft n.obj.X).map_injective hh

/-- Positive native alpha induction is actually faithful on every actual
simple orbit component of the internal-module category. -/
def componentPositiveFaithful :
    (ModuleAlphaInduction.positive Dᴹᵒᵖ
      (ModuleComponent.Component (C := Dᴹᵒᵖ) SM i)).Faithful where
  map_injective {X Y} f g h := by
    let n := ModuleComponent.base (C := Dᴹᵒᵖ) SM i
    letI := componentActionRightFaithful S SM i
    have hh := congrArg (fun t => t.val.app n) h
    exact (MonoidalLeftAction.actionRight Dᴹᵒᵖ n).map_injective hh

/-- Negative native alpha induction has the same faithful actual action
on morphisms, even though its actual strong lineator is different. -/
def componentNegativeFaithful :
    (ModuleAlphaInduction.negative Dᴹᵒᵖ
      (ModuleComponent.Component (C := Dᴹᵒᵖ) SM i)).Faithful where
  map_injective {X Y} f g h := by
    let n := ModuleComponent.base (C := Dᴹᵒᵖ) SM i
    letI := componentActionRightFaithful S SM i
    have hh := congrArg (fun t => t.val.app n) h
    exact (MonoidalLeftAction.actionRight Dᴹᵒᵖ n).map_injective hh

end Paper18.Category.GraphPicard
