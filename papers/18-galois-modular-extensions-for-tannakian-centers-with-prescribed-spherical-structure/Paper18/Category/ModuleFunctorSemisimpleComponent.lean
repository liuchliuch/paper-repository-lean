import Paper18.Category.ModuleFunctorSemisimpleCornerSkeleton
import Paper18.Category.ModuleComponentAction

/-! # Actual module-endofunctor corners on actual simple-orbit components -/
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

local instance componentKernels : HasKernels (ModuleComponent.Component (C := C) S i) :=
  ModuleComponent.hasKernels S i

/-- The actual strong additive linear inclusion of the actual component. -/
def componentInclusion : Bundled C (ModuleComponent.Component (C := C) S i) M where
  toFunctor := (ModuleComponent.property (C := C) S i).ι
  leftLinear := ModuleComponent.inclusionLeftLinear S i
  additive := inferInstance
  linear := inferInstance

instance componentInclusion_full : (componentInclusion (C := C) S i).toFunctor.Full :=
  inferInstanceAs ((ModuleComponent.property (C := C) S i).ι.Full)
instance componentInclusion_faithful : (componentInclusion (C := C) S i).toFunctor.Faithful :=
  inferInstanceAs ((ModuleComponent.property (C := C) S i).ι.Faithful)

/-- The actual semisimple right adjoint gives the actual module projection. -/
def componentProjection : Bundled C M (ModuleComponent.Component (C := C) S i) :=
  semisimpleRightAdjoint (ModuleComponent.skeleton S i) (componentInclusion S i)

def componentProjectionAdjunction :
    (componentInclusion (C := C) S i).toFunctor ⊣ (componentProjection (C := C) S i).toFunctor :=
  semisimpleRightAdjunction (ModuleComponent.skeleton S i) (componentInclusion S i)

instance componentProjection_unit_moduleNatural :
    IsModuleNatural C (componentProjectionAdjunction (C := C) S i).unit :=
  semisimpleRightAdjunction_unit_moduleNatural (ModuleComponent.skeleton S i) (componentInclusion S i)
instance componentProjection_counit_moduleNatural :
    IsModuleNatural C (componentProjectionAdjunction (C := C) S i).counit :=
  semisimpleRightAdjunction_counit_moduleNatural (ModuleComponent.skeleton S i) (componentInclusion S i)

/-- The actual component endofunctor is extended by the actual projection
and inclusion, with all native strong module data constructed. -/
def componentEndExtension :
    Bundled C (ModuleComponent.Component (C := C) S i) (ModuleComponent.Component (C := C) S i) ⥤
      Bundled C M M := cornerExtension (componentInclusion S i) (componentProjection S i)

def componentEndExtensionFullyFaithful :
    (componentEndExtension (C := C) S i).FullyFaithful :=
  cornerExtensionFullyFaithful (componentInclusion S i) (componentProjection S i)
    (componentProjectionAdjunction S i)

variable {ε : Type wE} [Fintype ε] (TE : FiniteSemisimpleSkeleton (Bundled C M M) ε)

/-- The finite actual simple classes of component module endofunctors. -/
abbrev ComponentEndSimpleIndex := CornerSimpleIndex (ModuleComponent.skeleton S i) S
  (componentInclusion S i) (componentProjection S i) (componentProjectionAdjunction S i) TE

/-- Actual finite semisimplicity on the component is derived from the
actual extension and the actual whole endofunctor skeleton. -/
def componentEndSkeleton : FiniteSemisimpleSkeleton
    (Bundled C (ModuleComponent.Component (C := C) S i) (ModuleComponent.Component (C := C) S i))
      (ComponentEndSimpleIndex S i TE) :=
  cornerEndSkeleton (ModuleComponent.skeleton S i) S
    (componentInclusion S i) (componentProjection S i) (componentProjectionAdjunction S i) TE

end Paper18.Category.ModuleFunctor
