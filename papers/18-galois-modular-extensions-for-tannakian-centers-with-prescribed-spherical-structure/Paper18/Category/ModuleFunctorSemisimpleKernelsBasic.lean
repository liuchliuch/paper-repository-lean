import Paper18.Category.ModuleFunctorAdjointStrong
import Paper18.Category.ModuleFunctorFiniteBasic
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! # The actual pointwise kernel and its strong module comparison -/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u v' u' v'' u''
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteLimits N] [MonoidalLeftAction C N]
  [∀ c : C, (actionLeft N c).Additive]
  [∀ c : C, (actionLeft N c).Linear ℂ]
  {F G : Bundled C M N} (τ : F ⟶ G)

/-- The genuine kernel in the ordinary functor category. -/
def moduleKernelUnderlying : M ⥤ N := kernel τ.val

instance moduleKernelUnderlying_additive : (moduleKernelUnderlying τ).Additive where
  map_add {m n} f g := by
    apply (cancel_mono ((kernel.ι τ.val).app n)).mp
    change (kernel τ.val).map (f + g) ≫ (kernel.ι τ.val).app n =
      ((kernel τ.val).map f + (kernel τ.val).map g) ≫ (kernel.ι τ.val).app n
    simp only [(kernel.ι τ.val).naturality, Preadditive.add_comp]
    erw [F.toFunctor.map_add]
    exact Preadditive.comp_add _ _ _ ((kernel.ι τ.val).app m)
      (F.toFunctor.map f) (F.toFunctor.map g)

instance moduleKernelUnderlying_linear : (moduleKernelUnderlying τ).Linear ℂ where
  map_smul {m n} f z := by
    apply (cancel_mono ((kernel.ι τ.val).app n)).mp
    change (kernel τ.val).map (z • f) ≫ (kernel.ι τ.val).app n =
      (z • (kernel τ.val).map f) ≫ (kernel.ι τ.val).app n
    simp only [(kernel.ι τ.val).naturality, Linear.smul_comp]
    erw [F.toFunctor.map_smul]
    exact Linear.comp_smul _ _ _ ((kernel.ι τ.val).app m) z (F.toFunctor.map f)

/-- Acting on the raw kernel and taking the raw kernel after acting agree
by the actual preserved kernel universal property and the actual strong
lineators of the two given module functors. -/
def moduleKernelLineatorIso (c : C) :
    moduleKernelUnderlying τ ⋙ actionLeft N c ≅ actionLeft M c ⋙ moduleKernelUnderlying τ := by
  letI := (actionAdjunction N c cᘁ).rightAdjoint_preservesLimits
  let R := (Functor.whiskeringRight M N N).obj (actionLeft N c)
  let L := (Functor.whiskeringLeft M M N).obj (actionLeft M c)
  letI : R.Additive := ⟨by intro X Y f g; ext m; exact (actionLeft N c).map_add⟩
  letI : L.Additive := ⟨by intros; rfl⟩
  exact PreservesKernel.iso R τ.val ≪≫
    kernel.mapIso (R.map τ.val) (L.map τ.val)
      (adjointActionLineatorIso F.toFunctor c) (adjointActionLineatorIso G.toFunctor c)
      (by ext m; exact (τ.property.lineator c m).symm) ≪≫
      (PreservesKernel.iso L τ.val).symm

/-- The actual kernel inclusion characterizes the induced lineator. -/
@[reassoc]
lemma moduleKernelLineatorIso_ι (c : C) (m : M) :
    (moduleKernelLineatorIso τ c).hom.app m ≫ (kernel.ι τ.val).app (c ⊙ₗ m) =
      (c ⊴ₗ (kernel.ι τ.val).app m) ≫ Functor.LaxLeftLinear.μₗ F.toFunctor c m := by
  letI := (actionAdjunction N c cᘁ).rightAdjoint_preservesLimits
  let R := (Functor.whiskeringRight M N N).obj (actionLeft N c)
  let L := (Functor.whiskeringLeft M M N).obj (actionLeft M c)
  letI : R.Additive := ⟨by intro X Y f g; ext m; exact (actionLeft N c).map_add⟩
  letI : L.Additive := ⟨by intros; rfl⟩
  have h : (moduleKernelLineatorIso τ c).hom ≫
      Functor.whiskerLeft (actionLeft M c) (kernel.ι τ.val) =
    Functor.whiskerRight (kernel.ι τ.val) (actionLeft N c) ≫
      (adjointActionLineatorIso F.toFunctor c).hom := by
    simp only [moduleKernelLineatorIso, Iso.trans_hom, Iso.symm_hom, assoc]
    erw [PreservesKernel.iso_inv_ι]
    simp [kernel.mapIso, kernel.map]
    erw [kernelComparison_comp_ι_assoc]
    rfl
  exact congrArg (fun a => a.app m) h

end Paper18.Category.ModuleFunctor
