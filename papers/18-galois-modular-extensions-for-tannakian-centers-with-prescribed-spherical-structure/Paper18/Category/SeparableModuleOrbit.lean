import Paper18.Category.SeparableModulesSemisimple
import Paper18.Category.InternalModuleAmbientFree
import Paper18.Category.ModuleComponentFunctorScalar
import Paper18.Category.MonoidalOppositeFusion

/-! # An actual nonempty component of a separable algebra's modules

The chosen component comes from a genuine simple summand of the regular
module. Its finite semisimplicity, native action and one-object generation
are constructed, with no indecomposability hypothesis on the whole module
category.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open MonoidalOpposite
open scoped BigOperators MonObj MonoidalLeftAction
universe v u w
namespace Paper18.Category.SeparableAlgebra
variable {D : Type u} [Category.{v} D] [Preadditive D] [Linear ℂ D]
  [MonoidalCategory D] [MonoidalPreadditive D] [MonoidalLinear ℂ D]
  [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)]
  {A : D} [MonObj A] (E : SeparableAlgebra A)
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

include E S in
/-- A nonzero algebra has an actual simple constituent in its regular
module, detected by the actual endomorphism Hom formula. -/
theorem regular_exists_simple_retract (hA : (𝟙 A : A ⟶ A) ≠ 0) :
    ∃ j : E.SimpleIndex S, Nonempty (Retract ((E.skeleton S).simpleObject j) (Mod_.regular A)) := by
  have hid : (𝟙 (Mod_.regular A) : Mod_.regular A ⟶ Mod_.regular A) ≠ 0 := by
    intro hz
    apply hA
    exact congrArg Mod_.Hom.hom hz
  have hp : 0 < Module.finrank ℂ (Mod_.regular A ⟶ Mod_.regular A) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 _, hid⟩
  rw [(E.skeleton S).finrank_hom_eq_sum] at hp
  obtain ⟨j, _, hj⟩ := Finset.sum_pos_iff.mp hp
  exact ⟨j, ((E.skeleton S).multiplicity_pos_iff_retract _ j).mp
    (Nat.pos_of_mul_pos_left hj)⟩

/-- A chosen label of an actual simple regular-module summand. -/
def orbitLabel (hA : (𝟙 A : A ⟶ A) ≠ 0) : E.SimpleIndex S :=
  Classical.choose (E.regular_exists_simple_retract S hA)

def orbitRegularRetract (hA : (𝟙 A : A ⟶ A) ≠ 0) :
    Retract ((E.skeleton S).simpleObject (E.orbitLabel S hA)) (Mod_.regular A) :=
  Classical.choice (Classical.choose_spec (E.regular_exists_simple_retract S hA))

attribute [local instance] InternalModule.ambientMonoidalOppositeLeftAction

/-- The actual simple-orbit component under native right ambient tensoring. -/
abbrev OrbitComponent (hA : (𝟙 A : A ⟶ A) ≠ 0) :=
  ModuleComponent.Component (C := Dᴹᵒᵖ) (E.skeleton S) (E.orbitLabel S hA)

def orbitSkeleton (hA : (𝟙 A : A ⟶ A) ≠ 0) :=
  ModuleComponent.skeleton (C := Dᴹᵒᵖ) (E.skeleton S) (E.orbitLabel S hA)

def orbitBase (hA : (𝟙 A : A ⟶ A) ≠ 0) : E.OrbitComponent S hA :=
  ModuleComponent.base (C := Dᴹᵒᵖ) (E.skeleton S) (E.orbitLabel S hA)

def orbitHasKernels (hA : (𝟙 A : A ⟶ A) ≠ 0) : HasKernels (E.OrbitComponent S hA) :=
  ModuleComponent.hasKernels (E.skeleton S) (E.orbitLabel S hA)

section Rigid
variable [BraidedCategory D] [RightRigidCategory D]
attribute [local instance] MonoidalOppositeFusion.rightRigidCategory

/-- Every actual orbit object is an actual retract of right tensoring
the chosen actual simple generator. -/
theorem orbit_retract_action_base (hA : (𝟙 A : A ⟶ A) ≠ 0)
    (M : E.OrbitComponent S hA) :
    ∃ X : Dᴹᵒᵖ, Nonempty (Retract M (X ⊙ₗ E.orbitBase S hA)) :=
  ModuleComponent.retract_action_base (E.skeleton S) (E.orbitLabel S hA) M

end Rigid
end Paper18.Category.SeparableAlgebra
