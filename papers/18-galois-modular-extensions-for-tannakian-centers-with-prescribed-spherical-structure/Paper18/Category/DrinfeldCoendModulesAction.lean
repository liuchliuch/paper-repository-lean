import Paper18.Category.DrinfeldCoendModulesTensorDesc
import Paper18.Category.DrinfeldCoendModulesActionComponent

/-! # Actual annular maps on central objects and full detection of morphisms

The maps are constructed by the proved coend universal property. Their
intertwining equation is proved equivalent to actual half-braiding naturality.
The algebra-action laws are established separately from this construction.
-/
noncomputable section
set_option maxHeartbeats 2000000
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w
namespace Paper18.Category.DrinfeldCoendModules
attribute [local instance 2000] RightRigidCategory.rightDual
variable {D : Type u} [Category.{v} D] [MonoidalCategory D] [BraidedCategory D]
  [RightRigidCategory D] [Preadditive D] [Linear ℂ D]
  [MonoidalPreadditive D] [MonoidalLinear ℂ D] [HasKernels D] [HasFiniteBiproducts D]
  [∀ X Y : D, FiniteDimensional ℂ (X ⟶ Y)] [Simple (𝟙_ D)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton D ι)

/-- The actual annular map, descended from its actual rigid cap family. -/
def action (Z : Center D) : algebra S ⊗ Z.1 ⟶ Z.1 :=
  tensorDesc S (actionComponent Z) (actionComponent_dinaturality Z)

@[reassoc]
lemma injection_action (Z : Center D) (T : D) :
    injection S T ▷ Z.1 ≫ action S Z = actionComponent Z T :=
  injection_tensorDesc S _ _ T

/-- The actual annular intertwining equation holds exactly for actual
morphisms of half-braided objects. -/
lemma action_comm_iff {Z W : Center D} (f : Z.1 ⟶ W.1) :
    action S Z ≫ f = algebra S ◁ f ≫ action S W ↔
      ∀ T : D, f ▷ T ≫ (W.2.β T).hom = (Z.2.β T).hom ≫ T ◁ f := by
  constructor
  · intro h T
    apply (actionComponent_comm_iff f T).mp
    have hh := congrArg (fun k => injection S T ▷ Z.1 ≫ k) h
    dsimp only at hh
    rw [injection_action_assoc, ← whisker_exchange_assoc, injection_action] at hh
    exact hh
  · intro h
    apply injection_tensor_hom_ext S
    intro T
    rw [injection_action_assoc, ← whisker_exchange_assoc, injection_action]
    exact (actionComponent_comm_iff f T).mpr (h T)

/-- Every actual center morphism intertwines the constructed actual
annular maps. -/
lemma action_naturality {Z W : Center D} (f : Z ⟶ W) :
    action S Z ≫ f.f = algebra S ◁ f.f ≫ action S W :=
  (action_comm_iff S f.f).mpr f.comm

end Paper18.Category.DrinfeldCoendModules
