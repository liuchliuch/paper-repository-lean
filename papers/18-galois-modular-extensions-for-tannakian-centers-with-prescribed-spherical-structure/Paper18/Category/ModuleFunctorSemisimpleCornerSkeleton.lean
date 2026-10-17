import Paper18.Category.ModuleFunctorSemisimpleCorner
import Paper18.Category.ModuleFunctorSemisimpleFoundation
import Paper18.Category.ModuleFunctorSemisimpleImage

/-! # Actual finite semisimplicity reflected to a module corner -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u vM uM vN uN wM wN wE
namespace Paper18.Category.ModuleFunctor
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type uM} [Category.{vM} M] [Preadditive M] [Linear ℂ M]
  [HasKernels M] [HasFiniteBiproducts M] [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C M]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft M c).Linear ℂ]
  {N : Type uN} [Category.{vN} N] [Preadditive N] [Linear ℂ N]
  [HasKernels N] [HasFiniteBiproducts N] [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalLeftAction C N]
  [∀ c : C, (MonoidalLeftAction.actionLeft N c).Additive]
  [∀ c : C, (MonoidalLeftAction.actionLeft N c).Linear ℂ]
  {ι : Type wM} [Fintype ι] (SM : FiniteSemisimpleSkeleton M ι)
  {κ : Type wN} [Fintype κ] (SN : FiniteSemisimpleSkeleton N κ)
  (I : Bundled C M N) [I.toFunctor.Full] [I.toFunctor.Faithful]
  (P : Bundled C N M) (adj : I.toFunctor ⊣ P.toFunctor)
  [IsModuleNatural C adj.unit] [IsModuleNatural C adj.counit]

attribute [local instance] Preadditive.hasEqualizers_of_hasKernels
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts
local instance cornerM_finiteLimits : HasFiniteLimits M :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products
local instance cornerN_finiteLimits : HasFiniteLimits N :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Actual evaluation and preservation of the actual simple splittings
prove monomorphism preservation of the genuine extension. -/
def cornerExtensionPreservesMonomorphisms : (cornerExtension I P).PreservesMonomorphisms where
  preserves {F G} τ _ := by
    letI : Mono τ.val := underlying_mono τ
    have hm (n : N) : Mono (I.toFunctor.map (τ.val.app (P.toFunctor.obj n))) := by
      letI : IsSplitMono (τ.val.app (P.toFunctor.obj n)) :=
        IsSplitMono.mk' (SM.splitMono _)
      infer_instance
    letI : ∀ n : N, Mono (((cornerExtension I P).map τ).val.app n) := hm
    letI : Mono (((cornerExtension I P).map τ).val) := NatTrans.mono_of_mono_app _
    exact (forget (C := C) (M := N) (N := N)).mono_of_mono_map
      (inferInstanceAs (Mono (((cornerExtension I P).map τ).val)))

variable {ε : Type wE} [Fintype ε]
  (TE : FiniteSemisimpleSkeleton (Bundled C N N) ε)

/-- The finite actual simple classes of endofunctors of this corner. -/
def CornerSimpleIndex := by
  letI : ∀ F G : Bundled C M M, FiniteDimensional ℂ (F ⟶ G) := finiteDimensionalHom SM
  letI : ∀ F G : Bundled C N N, FiniteDimensional ℂ (F ⟶ G) := finiteDimensionalHom SN
  letI := cornerExtension_faithful I P adj
  letI := cornerExtension_full I P adj
  letI := cornerExtensionPreservesMonomorphisms SM I P
  exact ImageSimpleIndex TE (cornerExtension I P)

instance cornerSimpleIndex_fintype : Fintype (CornerSimpleIndex SM SN I P adj TE) := by
  unfold CornerSimpleIndex
  infer_instance

/-- The actual whole-category endofunctor skeleton and the actual full
faithful corner extension derive actual finite semisimplicity of the corner. -/
def cornerEndSkeleton :
    FiniteSemisimpleSkeleton (Bundled C M M) (CornerSimpleIndex SM SN I P adj TE) := by
  letI : ∀ F G : Bundled C M M, FiniteDimensional ℂ (F ⟶ G) := finiteDimensionalHom SM
  letI : ∀ F G : Bundled C N N, FiniteDimensional ℂ (F ⟶ G) := finiteDimensionalHom SN
  letI := cornerExtension_faithful I P adj
  letI := cornerExtension_full I P adj
  letI := cornerExtensionPreservesMonomorphisms SM I P
  exact imageSkeleton TE (cornerExtension I P)

end Paper18.Category.ModuleFunctor
