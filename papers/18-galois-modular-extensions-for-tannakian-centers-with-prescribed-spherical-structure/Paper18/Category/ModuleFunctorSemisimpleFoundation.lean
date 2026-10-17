import Paper18.Category.ModuleFunctorSemisimpleKernelsUniversal
import Paper18.Category.ModuleFunctorSemisimpleBiproducts
import Paper18.Category.ModuleFunctorSemisimpleNatural
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-! # Actual finite limits and underlying splittings for module functors

The kernel and finite sum constructions give genuine finite limits. The
forgetful functor preserves them, so a monomorphism of actual module
functors is a monomorphism of ordinary functors. Its ordinary retraction
is constructed from the actual source simple decompositions. The
retraction is not asserted to be module natural here.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
open scoped MonoidalLeftAction
universe v u v' u' v'' u'' w w'
namespace Paper18.Category.ModuleFunctor
open MonoidalLeftAction
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [RightRigidCategory C]
  {M : Type u'} [Category.{v'} M] [Preadditive M] [Linear ℂ M]
  [MonoidalLeftAction C M]
  {N : Type u''} [Category.{v''} N] [Preadditive N] [Linear ℂ N]
  [HasFiniteLimits N] [MonoidalLeftAction C N]
  [∀ c : C, (actionLeft N c).Additive]
  [∀ c : C, (actionLeft N c).Linear ℂ]

attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts
attribute [local instance] Preadditive.hasEqualizers_of_hasKernels
attribute [local instance] hasBinaryBiproducts_of_finite_biproducts

/-- Actual finite limits of native strong additive linear module functors. -/
instance moduleFunctor_hasFiniteLimits : HasFiniteLimits (Bundled C M N) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- The genuine forgetful functor preserves these actual finite limits. -/
instance moduleForget_preservesFiniteLimits :
    PreservesFiniteLimits (forget (C := C) (M := M) (N := N)) :=
  Functor.preservesFiniteLimits_of_preservesKernels _

/-- In particular, an actual module monomorphism is an ordinary
natural-transformation monomorphism. -/
instance underlying_mono {F G : Bundled C M N} (τ : F ⟶ G) [Mono τ] : Mono τ.val :=
  inferInstanceAs (Mono ((forget (C := C) (M := M) (N := N)).map τ))

variable [HasKernels M] [HasFiniteBiproducts M]
  [∀ X Y : M, FiniteDimensional ℂ (X ⟶ Y)]
  [∀ X Y : N, FiniteDimensional ℂ (X ⟶ Y)]
  {ι : Type w} [Fintype ι] (S : FiniteSemisimpleSkeleton M ι)
  {κ : Type w'} [Fintype κ] (T : FiniteSemisimpleSkeleton N κ)

/-- The underlying ordinary retraction exists for every actual module
monomorphism, by actual simple-component splittings and linear extension. -/
def underlyingSplitMono {F G : Bundled C M N} (τ : F ⟶ G) [Mono τ] :
    SplitMono τ.val :=
  splitMonoNatural S F.toFunctor G.toFunctor T τ.val

end Paper18.Category.ModuleFunctor
