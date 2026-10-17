import Paper18.Category.GraphPicardComponentCharacter
import Paper18.Category.GraphPicardCapComparison

/-! # Genuine central transformations restricted to actual module components

The actual component action is a full restriction of the original action.
Thus actual module-natural transformations, and actual inverses when
present, restrict by their genuine components.
-/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w
namespace Paper18.Category.GraphPicard
section General
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {N : Type uM} [Category.{vM} N] [Preadditive N] [Linear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C N]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Additive]
  [∀ X : C, (MonoidalLeftAction.actionLeft N X).Linear ℂ]
  {κ : Type w} [Fintype κ] (SN : FiniteSemisimpleSkeleton N κ) (i : κ)
local notation "Comp" => ModuleComponent.Component (C := C) SN i

/-- An actual central-action transformation restricts to the actual full
simple component, retaining its actual module lineator equation. -/
def componentCentralHom {Z W : Center C}
    (q : ModuleAlphaInduction.centralEnd C N Z ⟶ ModuleAlphaInduction.centralEnd C N W) :
    ModuleAlphaInduction.centralEnd C Comp Z ⟶ ModuleAlphaInduction.centralEnd C Comp W :=
  ⟨{ app m := q.val.app m.obj
     naturality {m n} f := q.val.naturality (show m.obj ⟶ n.obj from f) },
    { lineator X m := by
        exact ModuleFunctor.IsModuleNatural.lineator (C := C) (τ := q.val) X m.obj }⟩

@[simp] lemma componentCentralHom_app {Z W : Center C}
    (q : ModuleAlphaInduction.centralEnd C N Z ⟶ ModuleAlphaInduction.centralEnd C N W)
    (m : Comp) : (componentCentralHom SN i q).val.app m = q.val.app m.obj := rfl

@[simp] lemma componentCentralHom_id (Z : Center C) :
    componentCentralHom SN i (𝟙 (ModuleAlphaInduction.centralEnd C N Z)) = 𝟙 _ := by
  apply ModuleFunctor.bundled_hom_ext
  ext m
  rfl

@[simp] lemma componentCentralHom_comp {Z W V : Center C}
    (q : ModuleAlphaInduction.centralEnd C N Z ⟶ ModuleAlphaInduction.centralEnd C N W)
    (r : ModuleAlphaInduction.centralEnd C N W ⟶ ModuleAlphaInduction.centralEnd C N V) :
    componentCentralHom SN i (q ≫ r) = componentCentralHom SN i q ≫ componentCentralHom SN i r := by
  apply ModuleFunctor.bundled_hom_ext
  ext m
  rfl

/-- Actual inverse central transformations restrict to actual inverses. -/
def componentCentralIso {Z W : Center C}
    (q : ModuleAlphaInduction.centralEnd C N Z ≅ ModuleAlphaInduction.centralEnd C N W) :
    ModuleAlphaInduction.centralEnd C Comp Z ≅ ModuleAlphaInduction.centralEnd C Comp W where
  hom := componentCentralHom SN i q.hom
  inv := componentCentralHom SN i q.inv
  hom_inv_id := by rw [← componentCentralHom_comp, Iso.hom_inv_id, componentCentralHom_id]
  inv_hom_id := by rw [← componentCentralHom_comp, Iso.inv_hom_id, componentCentralHom_id]
end General

end Paper18.Category.GraphPicard
