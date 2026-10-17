import Paper18.Category.ModuleFunctorSemisimpleKernelsBasic

/-! # Coherent actual kernels of strong module functors -/
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

/-- Naturality and coherence of the actual kernel comparison are forced
by its kernel inclusion, so no coherence data are supplied. -/
def moduleKernelLaxLeftLinear : (moduleKernelUnderlying τ).LaxLeftLinear C where
  μₗ c m := (moduleKernelLineatorIso τ c).hom.app m
  μₗ_naturality_left {c c'} f m := by
    apply (cancel_mono ((kernel.ι τ.val).app (c' ⊙ₗ m))).mp
    simp only [assoc]
    change (f ⊵ₗ (kernel τ.val).obj m) ≫ (moduleKernelLineatorIso τ c').hom.app m ≫
      (kernel.ι τ.val).app (c' ⊙ₗ m) =
        (moduleKernelLineatorIso τ c).hom.app m ≫ (kernel τ.val).map (f ⊵ₗ m) ≫
          (kernel.ι τ.val).app (c' ⊙ₗ m)
    rw [(kernel.ι τ.val).naturality]
    simp only [actionLeft_obj, moduleKernelLineatorIso_ι, moduleKernelLineatorIso_ι_assoc]
    rw [← action_exchange_assoc, Functor.LaxLeftLinear.μₗ_naturality_left]
  μₗ_naturality_right c {m n} f := (moduleKernelLineatorIso τ c).hom.naturality f
  μₗ_associativity c d m := by
    apply (cancel_mono ((kernel.ι τ.val).app (c ⊙ₗ d ⊙ₗ m))).mp
    simp only [assoc]
    change (moduleKernelLineatorIso τ (c ⊗ d)).hom.app m ≫
      (kernel τ.val).map (αₗ c d m).hom ≫ (kernel.ι τ.val).app (c ⊙ₗ d ⊙ₗ m) =
        (αₗ c d ((kernel τ.val).obj m)).hom ≫
          c ⊴ₗ (moduleKernelLineatorIso τ d).hom.app m ≫
            (moduleKernelLineatorIso τ c).hom.app (d ⊙ₗ m) ≫
              (kernel.ι τ.val).app (c ⊙ₗ d ⊙ₗ m)
    rw [(kernel.ι τ.val).naturality]
    simp only [actionLeft_obj, moduleKernelLineatorIso_ι, moduleKernelLineatorIso_ι_assoc]
    rw [← actionHomRight_comp_assoc, moduleKernelLineatorIso_ι, actionHomRight_comp]
    simp only [assoc]
    rw [Functor.LaxLeftLinear.μₗ_associativity]
    simp only [tensor_actionHomRight, assoc, Iso.inv_hom_id_assoc]
  μₗ_unitality m := by
    apply (cancel_mono ((kernel.ι τ.val).app m)).mp
    simp only [assoc]
    change (λₗ[C] ((kernel τ.val).obj m)).hom ≫ (kernel.ι τ.val).app m =
      (moduleKernelLineatorIso τ (𝟙_ C)).hom.app m ≫
        (kernel τ.val).map (λₗ[C] m).hom ≫ (kernel.ι τ.val).app m
    rw [(kernel.ι τ.val).naturality]
    simp only [actionLeft_obj]
    rw [moduleKernelLineatorIso_ι_assoc, ← Functor.LaxLeftLinear.μₗ_unitality]
    exact actionUnitIso_hom_naturality _

/-- The raw kernel has the actual strong native module structure. -/
def moduleKernelLeftLinear : (moduleKernelUnderlying τ).LeftLinear C := by
  letI := moduleKernelLaxLeftLinear τ
  letI (c : C) (m : M) : IsIso (Functor.LaxLeftLinear.μₗ (moduleKernelUnderlying τ) c m) := by
    change IsIso ((moduleKernelLineatorIso τ c).hom.app m)
    infer_instance
  exact leftLinearOfLax (moduleKernelUnderlying τ)

/-- The actual kernel object in the category of strong complex-linear
module functors. -/
def moduleKernel : Bundled C M N where
  toFunctor := moduleKernelUnderlying τ
  leftLinear := moduleKernelLeftLinear τ
  additive := inferInstance
  linear := inferInstance

/-- The actual pointwise kernel inclusion is module natural. -/
def moduleKernelι : moduleKernel τ ⟶ F :=
  ⟨kernel.ι τ.val, ⟨fun c m => moduleKernelLineatorIso_ι τ c m⟩⟩

@[reassoc (attr := simp)]
lemma moduleKernelι_condition : moduleKernelι τ ≫ τ = 0 := by
  apply Subtype.ext
  exact kernel.condition τ.val

end Paper18.Category.ModuleFunctor
