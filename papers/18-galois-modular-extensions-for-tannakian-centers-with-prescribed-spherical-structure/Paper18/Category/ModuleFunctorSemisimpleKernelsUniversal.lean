import Paper18.Category.ModuleFunctorSemisimpleKernels

/-! # The actual universal kernel in the module-functor category -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteLimits N] [MonoidalLeftAction C N]
  [∀ c : C, (actionLeft N c).Additive]
  [∀ c : C, (actionLeft N c).Linear ℂ]
  {F G : Bundled C M N} (τ : F ⟶ G)

/-- An actual vanishing module transformation factors through the actual
underlying kernel, and the kernel inclusion forces module naturality. -/
def moduleKernelLift {Z : Bundled C M N} (k : Z ⟶ F) (hk : k ≫ τ = 0) :
    Z ⟶ moduleKernel τ := by
  have hk' : k.val ≫ τ.val = 0 := congrArg (fun f : Z ⟶ G => f.val) hk
  let h := kernel.lift τ.val k.val hk'
  have hl (m : M) : h.app m ≫ (kernel.ι τ.val).app m = k.val.app m :=
    congrArg (fun a => a.app m) (kernel.lift_ι τ.val k.val hk')
  refine ⟨h, ⟨fun c m => ?_⟩⟩
  apply (cancel_mono ((kernel.ι τ.val).app (c ⊙ₗ m))).mp
  simp only [assoc]
  change Functor.LaxLeftLinear.μₗ Z.toFunctor c m ≫ h.app (c ⊙ₗ m) ≫
    (kernel.ι τ.val).app (c ⊙ₗ m) =
      (c ⊴ₗ h.app m) ≫ (moduleKernelLineatorIso τ c).hom.app m ≫
        (kernel.ι τ.val).app (c ⊙ₗ m)
  rw [hl, moduleKernelLineatorIso_ι, ← actionHomRight_comp_assoc, hl]
  exact k.property.lineator c m

@[reassoc (attr := simp)]
lemma moduleKernelLift_ι {Z : Bundled C M N} (k : Z ⟶ F) (hk : k ≫ τ = 0) :
    moduleKernelLift τ k hk ≫ moduleKernelι τ = k := by
  apply Subtype.ext
  exact kernel.lift_ι _ _ _

instance moduleKernelι_mono : Mono (moduleKernelι τ) :=
  (forget (C := C) (M := M) (N := N)).mono_of_mono_map
    (inferInstanceAs (Mono (kernel.ι τ.val)))

/-- The actual kernel universal property in the native strong module
functor category. -/
def moduleKernelIsLimit :
    IsLimit (KernelFork.ofι (moduleKernelι τ) (moduleKernelι_condition τ)) :=
  KernelFork.IsLimit.ofι' _ _ (fun k hk =>
    ⟨moduleKernelLift τ k hk, moduleKernelLift_ι τ k hk⟩)

instance moduleFunctor_hasKernel : HasKernel τ where
  exists_limit := ⟨⟨KernelFork.ofι (moduleKernelι τ) (moduleKernelι_condition τ),
    moduleKernelIsLimit τ⟩⟩

instance moduleFunctor_hasKernels : HasKernels (Bundled C M N) where
  has_limit τ := moduleFunctor_hasKernel τ

/-- Forgetting the native module structure preserves the constructed
actual kernels. -/
instance moduleForget_preservesKernel :
    PreservesLimit (parallelPair τ 0) (forget (C := C) (M := M) (N := N)) := by
  apply preservesLimit_of_preserves_limit_cone (moduleKernelIsLimit τ)
  exact (KernelFork.isLimitMapConeEquiv
    (KernelFork.ofι (moduleKernelι τ) (moduleKernelι_condition τ))
      (forget (C := C) (M := M) (N := N))).symm (kernelIsKernel τ.val)

end Paper18.Category.ModuleFunctor
