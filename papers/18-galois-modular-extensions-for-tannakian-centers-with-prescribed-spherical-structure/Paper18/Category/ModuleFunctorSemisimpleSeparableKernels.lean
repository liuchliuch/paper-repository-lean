import Paper18.Category.ModuleFunctorSemisimpleSeparableLinear
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # Actual kernels for modules in a native action category -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory CategoryTheory.Limits
open scoped MonObj MonoidalLeftAction
universe v u v' u'
namespace Paper18.Category.ModuleFunctor.SeparableAction
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  [∀ c : C, (actionLeft M c).Additive]
  [∀ c : C, (actionLeft M c).Linear ℂ]
  [HasKernels M] {A : C} [MonObj A]
  {X Y : Mod_ M A} (f : X ⟶ Y)

/-- The ambient kernel inherits the actual action by the kernel universal
property applied to the original module action. -/
def kernelAction : A ⊙ₗ kernel f.hom ⟶ kernel f.hom :=
  kernel.lift f.hom ((A ⊴ₗ kernel.ι f.hom) ≫ γ[A,X.X]) (by
    have hf : γ[A,X.X] ≫ f.hom = (A ⊴ₗ f.hom) ≫ γ[A,Y.X] :=
      IsMod_Hom.smul_hom (A := A) (f := f.hom)
    rw [Category.assoc, hf, ← actionHomRight_comp_assoc, kernel.condition]
    simp)

omit [Linear ℂ M] [∀ c : C, (actionLeft M c).Linear ℂ] in
@[reassoc (attr := simp)]
theorem kernelAction_ι : kernelAction f ≫ kernel.ι f.hom =
    (A ⊴ₗ kernel.ι f.hom) ≫ γ[A,X.X] := kernel.lift_ι _ _ _

/-- The actual kernel module. -/
def kernelObj : Mod_ M A :=
  letI : ModObj A (kernel f.hom) :=
    { smul := kernelAction f
      one_smul' := by
        apply (cancel_mono (kernel.ι f.hom)).mp
        rw [Category.assoc, kernelAction_ι, ← action_exchange_assoc, ModObj.one_smul]
        exact (actionUnitIso_hom_naturality _).symm
      mul_smul' := by
        apply (cancel_mono (kernel.ι f.hom)).mp
        simp only [Category.assoc, kernelAction_ι]
        rw [← action_exchange_assoc, ModObj.mul_smul, action_assoc_naturality_assoc,
          ← actionHomRight_comp_assoc, ← kernelAction_ι, actionHomRight_comp]
        simp only [Category.assoc, kernelAction_ι] }
  ⟨kernel f.hom⟩

/-- The actual equivariant inclusion of the kernel module. -/
def kernelι : kernelObj f ⟶ X :=
  Mod_.Hom.mk' (kernel.ι f.hom) (kernelAction_ι f)

omit [Linear ℂ M] [∀ c : C, (actionLeft M c).Linear ℂ] in
@[simp] theorem kernelι_hom : (kernelι f).hom = kernel.ι f.hom := rfl

@[reassoc (attr := simp)]
theorem kernelι_condition : kernelι f ≫ f = 0 := by
  apply Mod_.Hom.ext
  exact kernel.condition f.hom

/-- The ambient universal kernel lift is an actual module morphism. -/
def kernelLift {P : Mod_ M A} (k : P ⟶ X) (hk : k ≫ f = 0) : P ⟶ kernelObj f :=
  Mod_.Hom.mk' (kernel.lift f.hom k.hom (by simpa using congrArg Mod_.Hom.hom hk)) (by
    change γ[A,P.X] ≫ kernel.lift f.hom k.hom _ =
      (A ⊴ₗ kernel.lift f.hom k.hom _) ≫ kernelAction f
    apply (cancel_mono (kernel.ι f.hom)).mp
    simp only [Category.assoc, kernel.lift_ι, kernelAction_ι]
    rw [← actionHomRight_comp_assoc, kernel.lift_ι]
    exact IsMod_Hom.smul_hom (A := A) (f := k.hom))

@[reassoc (attr := simp)]
theorem kernelLift_ι {P : Mod_ M A} (k : P ⟶ X) (hk : k ≫ f = 0) :
    kernelLift f k hk ≫ kernelι f = k := by
  apply Mod_.Hom.ext
  exact kernel.lift_ι _ _ _

instance kernelι_mono : Mono (kernelι f) :=
  (Mod_.forget (D := M) A).mono_of_mono_map (inferInstance : Mono (kernel.ι f.hom))

/-- The actual kernel module satisfies the universal property. -/
def kernelIsLimit : IsLimit (KernelFork.ofι (kernelι f) (kernelι_condition f)) :=
  KernelFork.IsLimit.ofι' _ _ (fun k hk => ⟨kernelLift f k hk, kernelLift_ι f k hk⟩)

instance hasKernel : HasKernel f where
  exists_limit := ⟨⟨KernelFork.ofι (kernelι f) (kernelι_condition f), kernelIsLimit f⟩⟩

instance hasKernels : HasKernels (Mod_ M A) where
  has_limit f := hasKernel f

/-- The actual forgetful functor preserves the kernel just constructed. -/
instance forget_preservesKernel : PreservesLimit (parallelPair f 0) (Mod_.forget (D := M) A) := by
  apply preservesLimit_of_preserves_limit_cone (kernelIsLimit f)
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (kernelι f) (kernelι_condition f))
      (Mod_.forget (D := M) A)).symm (kernelIsKernel f.hom)

end Paper18.Category.ModuleFunctor.SeparableAction
