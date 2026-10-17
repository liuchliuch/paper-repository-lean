import Paper18.Category.SeparableModulesLinear
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Actual kernels of internal module morphisms -/
noncomputable section
open Classical CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj
universe v u
namespace Paper18.Category.InternalModule
variable {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] {A : C} [MonObj A]
  {M N : Mod_ C A} (f : M ⟶ N)

/-- The ambient kernel inherits the actual action by the kernel universal
property applied to the original module action. -/
def kernelAction : A ⊗ kernel f.hom ⟶ kernel f.hom :=
  kernel.lift f.hom ((A ◁ kernel.ι f.hom) ≫ γ[A,M.X]) (by
    have hf : γ[A,M.X] ≫ f.hom = (A ◁ f.hom) ≫ γ[A,N.X] :=
      IsMod_Hom.smul_hom (A := A) (f := f.hom)
    rw [Category.assoc, hf, ← whiskerLeft_comp_assoc, kernel.condition]
    simp)

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
@[reassoc (attr := simp)]
theorem kernelAction_ι : kernelAction f ≫ kernel.ι f.hom =
    (A ◁ kernel.ι f.hom) ≫ γ[A,M.X] := kernel.lift_ι _ _ _

/-- The actual kernel module. -/
def kernelObj : Mod_ C A :=
  letI : ModObj A (kernel f.hom) :=
    { smul := kernelAction f
      one_smul' := by
        change η[A] ▷ kernel f.hom ≫ kernelAction f = (λ_ (kernel f.hom)).hom
        apply (cancel_mono (kernel.ι f.hom)).mp
        rw [Category.assoc, kernelAction_ι, ← whisker_exchange_assoc, one_smul]
        exact leftUnitor_naturality _
      mul_smul' := by
        change μ[A] ▷ kernel f.hom ≫ kernelAction f =
          (α_ A A (kernel f.hom)).hom ≫ (A ◁ kernelAction f) ≫ kernelAction f
        apply (cancel_mono (kernel.ι f.hom)).mp
        simp only [Category.assoc, kernelAction_ι]
        rw [← whisker_exchange_assoc, mul_smul, associator_naturality_right_assoc,
          ← whiskerLeft_comp_assoc, ← kernelAction_ι, whiskerLeft_comp]
        simp only [Category.assoc, kernelAction_ι] }
  ⟨kernel f.hom⟩

/-- The actual equivariant inclusion of the kernel module. -/
def kernelι : kernelObj f ⟶ M :=
  Mod_.Hom.mk' (kernel.ι f.hom) (kernelAction_ι f)

omit [Linear ℂ C] [MonoidalLinear ℂ C] in
@[simp] theorem kernelι_hom : (kernelι f).hom = kernel.ι f.hom := rfl

@[reassoc (attr := simp)]
theorem kernelι_condition : kernelι f ≫ f = 0 := by
  apply Mod_.Hom.ext
  exact kernel.condition f.hom

/-- The ambient universal kernel lift is an actual module morphism. -/
def kernelLift {P : Mod_ C A} (k : P ⟶ M) (hk : k ≫ f = 0) : P ⟶ kernelObj f :=
  Mod_.Hom.mk' (kernel.lift f.hom k.hom (by simpa using congrArg Mod_.Hom.hom hk)) (by
    change γ[A,P.X] ≫ kernel.lift f.hom k.hom _ =
      (A ◁ kernel.lift f.hom k.hom _) ≫ kernelAction f
    apply (cancel_mono (kernel.ι f.hom)).mp
    simp only [Category.assoc, kernel.lift_ι, kernelAction_ι]
    rw [← whiskerLeft_comp_assoc, kernel.lift_ι]
    exact IsMod_Hom.smul_hom (A := A) (f := k.hom))

@[reassoc (attr := simp)]
theorem kernelLift_ι {P : Mod_ C A} (k : P ⟶ M) (hk : k ≫ f = 0) :
    kernelLift f k hk ≫ kernelι f = k := by
  apply Mod_.Hom.ext
  exact kernel.lift_ι _ _ _

instance kernelι_mono : Mono (kernelι f) :=
  (Mod_.forget (D := C) A).mono_of_mono_map (inferInstance : Mono (kernel.ι f.hom))

/-- The actual kernel module satisfies the universal property. -/
def kernelIsLimit : IsLimit (KernelFork.ofι (kernelι f) (kernelι_condition f)) :=
  KernelFork.IsLimit.ofι' _ _ (fun k hk => ⟨kernelLift f k hk, kernelLift_ι f k hk⟩)

instance hasKernel : HasKernel f where
  exists_limit := ⟨⟨KernelFork.ofι (kernelι f) (kernelι_condition f), kernelIsLimit f⟩⟩

instance hasKernels : HasKernels (Mod_ C A) where
  has_limit f := hasKernel f

/-- The actual forgetful functor preserves the kernel just constructed. -/
instance forget_preservesKernel : PreservesLimit (parallelPair f 0) (Mod_.forget (D := C) A) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (kernelι f) (kernelι_condition f))
      (Mod_.forget (D := C) A)).symm (kernelIsKernel f.hom)

end Paper18.Category.InternalModule
