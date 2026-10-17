import Paper18.Category.ModuleFunctorSemisimpleComponent
import Paper18.Category.ModuleComponentScalar
import Paper18.Category.ModuleFunctorAdjointEnd

/-! # The actual tensor unit of component module endofunctors is simple -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w wE
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Linear ℂ]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι) (i : ι)

local instance componentUnitKernels : HasKernels (ModuleComponent.Component (C := C) S i) :=
  ModuleComponent.hasKernels S i
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels
local instance componentUnitFiniteLimits : HasFiniteLimits (ModuleComponent.Component (C := C) S i) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Actual one-object detection bounds the actual identity-module
endomorphism space by the one-dimensional endomorphisms of the base simple. -/
lemma componentEndUnit_finrank :
    Module.finrank ℂ (𝟙_ (ModuleAlphaInduction.End C (ModuleComponent.Component (C := C) S i)) ⟶
      𝟙_ (ModuleAlphaInduction.End C (ModuleComponent.Component (C := C) S i))) = 1 := by
  let E := ModuleAlphaInduction.endUnit C (ModuleComponent.Component (C := C) S i)
  letI : ∀ F G : Bundled C (ModuleComponent.Component (C := C) S i)
      (ModuleComponent.Component (C := C) S i), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (ModuleComponent.skeleton S i)
  have hle := ModuleComponent.hom_finrank_le S i E E
  change Module.finrank ℂ (E ⟶ E) ≤
    Module.finrank ℂ (ModuleComponent.base (C := C) S i ⟶ ModuleComponent.base (C := C) S i) at hle
  rw [CategoryTheory.finrank_endomorphism_simple_eq_one ℂ (ModuleComponent.base (C := C) S i)] at hle
  have hn : (𝟙 E : E ⟶ E) ≠ 0 := by
    intro hz
    have h := congrArg (fun f : E ⟶ E => f.val.app (ModuleComponent.base (C := C) S i)) hz
    change (𝟙 (ModuleComponent.base (C := C) S i)) = 0 at h
    exact CategoryTheory.id_nonzero _ h
  have hp : 0 < Module.finrank ℂ (E ⟶ E) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr ⟨𝟙 E, hn⟩
  change Module.finrank ℂ (E ⟶ E) = 1
  omega

variable {ε : Type wE} [Fintype ε]
  (TE : FiniteSemisimpleSkeleton
    (ModuleAlphaInduction.End C (ModuleComponent.Component (C := C) S i)) ε)

/-- Simplicity of the actual tensor unit follows from the derived actual
endomorphism dimension, using the actual component endofunctor skeleton. -/
def componentEndUnit_simple :
    Simple (𝟙_ (ModuleAlphaInduction.End C (ModuleComponent.Component (C := C) S i))) := by
  letI : ∀ F G : Bundled C (ModuleComponent.Component (C := C) S i)
      (ModuleComponent.Component (C := C) S i), FiniteDimensional ℂ (F ⟶ G) :=
    finiteDimensionalHom (ModuleComponent.skeleton S i)
  exact TE.simple_of_finrank_end_eq_one _ (componentEndUnit_finrank S i)

end Paper18.Category.ModuleFunctor
