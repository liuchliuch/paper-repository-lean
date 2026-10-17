import Paper18.Category.ModuleFunctorSemisimpleComponent
import Paper18.Category.ModuleFunctorDualDimensionBlockAlgebra

/-! # The genuine component projector is a subfunctor of the identity -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM w
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Linear ℂ]
  {κ : Type w} [Fintype κ] (SM : FiniteSemisimpleSkeleton M κ) (j : κ)

omit [∀ c : C, (MonoidalLeftAction.actionLeft M c).Linear ℂ] in
/-- The actual counit has no kernel: that kernel lies in the actual
component, where the adjunction identifies its map with zero. -/
lemma componentProjection_counit_mono (Y : M) :
    Mono ((componentProjectionAdjunction (C := C) SM j).counit.app Y) := by
  let adj := componentProjectionAdjunction (C := C) SM j
  let ε := adj.counit.app Y
  apply Preadditive.mono_of_kernel_zero
  let q : Retract (kernel ε) ((componentInclusion (C := C) SM j).toFunctor.obj
      ((componentProjection (C := C) SM j).toFunctor.obj Y)) :=
    ⟨kernel.ι ε, (SM.splitMono (kernel.ι ε)).retraction, (SM.splitMono (kernel.ι ε)).id⟩
  have hK : ModuleComponent.property (C := C) SM j (kernel ε) :=
    IsAdditiveFullProperty.of_retract q ((componentProjection (C := C) SM j).toFunctor.obj Y).property
  let K : ModuleComponent.Component (C := C) SM j := ⟨kernel ε, hK⟩
  let k : K ⟶ (componentProjection (C := C) SM j).toFunctor.obj Y := kernel.ι ε
  have hk : k = 0 := by
    apply (adj.homEquiv K Y).symm.injective
    rw [adj.homEquiv_counit, adj.homEquiv_counit]
    change kernel.ι ε ≫ ε = 0 ≫ ε
    simp only [kernel.condition, zero_comp]
  exact hk

include SM j in
/-- The actual ordinary projector as a genuine strong module endofunctor. -/
def componentProjectionEnd : ModuleAlphaInduction.End C M where
  toFunctor := (componentProjection (C := C) SM j).toFunctor ⋙ (componentInclusion (C := C) SM j).toFunctor
  leftLinear := inferInstance
  additive := inferInstance
  linear := inferInstance

/-- Its actual inclusion into the identity is native module natural. -/
def componentProjectionCounit : componentProjectionEnd (C := C) SM j ⟶ ModuleAlphaInduction.endUnit C M :=
  ⟨(componentProjectionAdjunction (C := C) SM j).counit,
    show IsModuleNatural C (componentProjectionAdjunction (C := C) SM j).counit from inferInstance⟩

/-- This is an actual subobject of the tensor unit in the actual End category. -/
instance componentProjectionCounit_mono : Mono (componentProjectionCounit (C := C) SM j) := by
  letI (Y : M) : Mono ((componentProjectionAdjunction (C := C) SM j).counit.app Y) :=
    componentProjection_counit_mono SM j Y
  letI : Mono (componentProjectionAdjunction (C := C) SM j).counit :=
    NatTrans.mono_of_mono_app _
  exact (forget (C := C) (M := M) (N := M)).mono_of_mono_map
    (inferInstanceAs (Mono (componentProjectionAdjunction (C := C) SM j).counit))

end Paper18.Category.ModuleFunctor
