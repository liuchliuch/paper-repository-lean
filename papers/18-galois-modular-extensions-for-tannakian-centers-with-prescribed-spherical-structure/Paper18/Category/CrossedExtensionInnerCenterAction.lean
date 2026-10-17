import Paper18.Category.CrossedExtensionCenterAction
import Paper18.Category.CrossedExtensionInnerNormalizationComposition
import Paper18.Category.WeakActionQuotientStandardActionTransport
import Paper18.Category.DrinfeldEquivalenceMapActionIso

/-! # The canonical push action and its actual center normalization -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCenterActionKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The constructed canonical push functors form an actual weak action.
Its pentagon and unit laws follow from the proved normalization squares. -/
def canonicalKernelAction : WeakAction (KillingExtension G) (CocycleVec (kernelCocycle ω)) :=
  WeakAction.ofIsoFamilyMul (kernelAction ω) (canonicalKernelPush ω)
    (kernelPushNormalization ω) (canonicalKernelPushMul ω) (kernelPushNormalization_comp ω)

instance canonicalKernelAction_rho_monoidal (g : KillingExtension G) :
    ((canonicalKernelAction ω).ρ g).Monoidal :=
  inferInstanceAs (canonicalKernelPush ω g).Monoidal

instance canonicalKernelAction_rho_additive (g : KillingExtension G) :
    ((canonicalKernelAction ω).ρ g).Additive :=
  inferInstanceAs (canonicalKernelPush ω g).Additive

instance canonicalKernelAction_rho_linear (g : KillingExtension G) :
    ((canonicalKernelAction ω).ρ g).Linear ℂ :=
  inferInstanceAs ((canonicalKernelPush ω g).Linear ℂ)

instance canonicalKernelAction_isMonoidal : (canonicalKernelAction ω).IsMonoidal := by
  unfold canonicalKernelAction
  infer_instance

@[simp] lemma canonicalKernelAction_rho (g : KillingExtension G) :
    (canonicalKernelAction ω).ρ g = canonicalKernelPush ω g := rfl

@[simp] lemma canonicalKernelAction_mulIso (g h : KillingExtension G) :
    (canonicalKernelAction ω).mulIso g h = canonicalKernelPushMul ω g h := rfl

/-- The explicit normalization is an actual monoidal isomorphism of
weak actions, with its coherence inherited from the proved component square. -/
def kernelActionNormalization : WeakAction.ActionIso (kernelAction ω) (canonicalKernelAction ω) :=
  WeakAction.ofIsoFamilyMulActionIso (kernelAction ω) (canonicalKernelPush ω)
    (kernelPushNormalization ω) (canonicalKernelPushMul ω) (kernelPushNormalization_comp ω)

instance kernelActionNormalization_monoidal : (kernelActionNormalization ω).IsMonoidal := by
  unfold kernelActionNormalization
  infer_instance

@[simp] lemma kernelActionNormalization_iso (g : KillingExtension G) :
    (kernelActionNormalization ω).iso g = kernelPushNormalization ω g := rfl

/-- The actual braided strong monoidal center action in canonical push convention. -/
def canonicalKernelCenterAction :
    WeakAction (KillingExtension G) (Center (CocycleVec (kernelCocycle ω))) :=
  DrinfeldEquivalence.centerAction (canonicalKernelAction ω)

instance canonicalKernelCenterAction_rho_monoidal (g : KillingExtension G) :
    ((canonicalKernelCenterAction ω).ρ g).Monoidal :=
  inferInstanceAs ((DrinfeldEquivalence.centerAction (canonicalKernelAction ω)).ρ g).Monoidal

instance canonicalKernelCenterAction_rho_braided (g : KillingExtension G) :
    ((canonicalKernelCenterAction ω).ρ g).Braided :=
  inferInstanceAs ((DrinfeldEquivalence.centerAction (canonicalKernelAction ω)).ρ g).Braided

instance canonicalKernelCenterAction_rho_additive (g : KillingExtension G) :
    ((canonicalKernelCenterAction ω).ρ g).Additive :=
  inferInstanceAs ((DrinfeldEquivalence.centerAction (canonicalKernelAction ω)).ρ g).Additive

instance canonicalKernelCenterAction_rho_linear (g : KillingExtension G) :
    ((canonicalKernelCenterAction ω).ρ g).Linear ℂ :=
  inferInstanceAs (((DrinfeldEquivalence.centerAction (canonicalKernelAction ω)).ρ g).Linear ℂ)

instance canonicalKernelCenterAction_isMonoidal : (canonicalKernelCenterAction ω).IsMonoidal :=
  DrinfeldEquivalence.centerAction_isMonoidal (canonicalKernelAction ω)

/-- The original center action and the canonical push center action are
actually coherently monoidally isomorphic. -/
def kernelCenterActionNormalization :
    WeakAction.ActionIso (kernelCenterAction ω) (canonicalKernelCenterAction ω) :=
  DrinfeldEquivalence.centerActionIso (kernelActionNormalization ω)

instance kernelCenterActionNormalization_monoidal :
    (kernelCenterActionNormalization ω).IsMonoidal :=
  DrinfeldEquivalence.centerActionIso_monoidal (kernelActionNormalization ω)

@[simp] lemma kernelCenterActionNormalization_iso_hom_app_f (g : KillingExtension G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (((kernelCenterActionNormalization ω).iso g).hom.app Z).f =
      (kernelPushNormalization ω g).hom.app Z.1 := rfl

end Paper18.Category.CrossedExtension
