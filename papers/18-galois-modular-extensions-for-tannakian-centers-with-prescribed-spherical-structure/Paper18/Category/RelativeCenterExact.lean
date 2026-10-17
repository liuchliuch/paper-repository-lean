import Paper18.Category.RelativeCenterKernels
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
import Mathlib.CategoryTheory.Simple
import Mathlib.CategoryTheory.Idempotents.Basic

/-!
# Exactness of forgetting and simple canonical lifts

The center's forgetful functor preserves finite limits because its actual
kernels and finite direct sums have been constructed. Hence an object whose
underlying object is simple is actually simple in the center.
-/
noncomputable section
universe v u
namespace Paper18.Category.RelativeCenter
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]
  [RightRigidCategory C] [LeftRigidCategory C]
  [Preadditive C] [Linear ℂ C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  {P : ObjectProperty C} [P.IsMonoidal]

instance center_hasEqualizers : HasEqualizers (RelativeCenter P) :=
  Preadditive.hasEqualizers_of_hasKernels

instance center_hasBinaryBiproducts : HasBinaryBiproducts (RelativeCenter P) :=
  hasBinaryBiproducts_of_finite_biproducts _

instance center_hasFiniteLimits : HasFiniteLimits (RelativeCenter P) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products

/-- Idempotents of actual central morphisms split inside the center. -/
instance center_isIdempotentComplete : IsIdempotentComplete (RelativeCenter P) := by
  rw [Idempotents.isIdempotentComplete_iff_idempotents_have_kernels]
  intros
  infer_instance

instance forget_preservesFiniteLimits : PreservesFiniteLimits (forget P) :=
  Functor.preservesFiniteLimits_of_preservesKernels (forget P)

instance forget_preservesMonomorphisms : (forget P).PreservesMonomorphisms :=
  inferInstance

/-- Simplicity of an underlying object implies actual simplicity in the
center. This uses preserved monomorphisms, rather than an assumed list of
central simple objects. -/
theorem simple_of_underlying_simple (Z : RelativeCenter P) [Simple Z.1] : Simple Z where
  mono_isIso_iff_nonzero {Y} f := by
    intro hfmono
    letI := hfmono
    haveI : Mono f.f := inferInstanceAs (Mono ((forget P).map f))
    constructor
    · intro hf hzero
      haveI := hf
      haveI : IsIso f.f := inferInstanceAs (IsIso ((forget P).map f))
      have hn := (Simple.mono_isIso_iff_nonzero f.f).mp (by infer_instance)
      exact hn (by rw [hzero]; rfl)
    · intro hn
      have hn' : f.f ≠ 0 := by
        intro h
        apply hn
        apply ext P
        exact h
      haveI : IsIso f.f := isIso_of_mono_of_nonzero hn'
      infer_instance

instance unit_simple [Simple (𝟙_ C)] : Simple (𝟙_ (RelativeCenter P)) := by
  letI : Simple ((𝟙_ (RelativeCenter P)).1) := inferInstanceAs (Simple (𝟙_ C))
  exact simple_of_underlying_simple _

end Paper18.Category.RelativeCenter
