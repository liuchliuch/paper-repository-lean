import Paper18.Category.CrossedExtensionActionMonoidal
import Paper18.Category.QuasiFusionCenter
import Paper18.Category.DrinfeldEquivalenceMapAction
import Paper18.Category.DrinfeldEquivalenceMapLinear

/-! # The actual center action of the finite killing extension -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance centerActionKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The actual coherent braided strong monoidal action on the actual
positive integral nondegenerate center of the kernel fusion category. -/
def kernelCenterAction : WeakAction (KillingExtension G) (Center (CocycleVec (kernelCocycle ω))) :=
  DrinfeldEquivalence.centerAction (kernelAction ω)

instance kernelCenterAction_rho_monoidal (g : KillingExtension G) :
    ((kernelCenterAction ω).ρ g).Monoidal :=
  DrinfeldEquivalence.centerAction_rho_monoidal (kernelAction ω) g

instance kernelCenterAction_rho_braided (g : KillingExtension G) :
    ((kernelCenterAction ω).ρ g).Braided :=
  DrinfeldEquivalence.centerAction_rho_braided (kernelAction ω) g

instance kernelCenterAction_isMonoidal : (kernelCenterAction ω).IsMonoidal :=
  DrinfeldEquivalence.centerAction_isMonoidal (kernelAction ω)

instance kernelCenterAction_rho_additive (g : KillingExtension G) :
    ((kernelCenterAction ω).ρ g).Additive :=
  inferInstanceAs ((DrinfeldEquivalence.map ((kernelAction ω).ρ g)).Additive)

instance kernelCenterAction_rho_linear (g : KillingExtension G) :
    ((kernelCenterAction ω).ρ g).Linear ℂ :=
  inferInstanceAs ((DrinfeldEquivalence.map ((kernelAction ω).ρ g)).Linear ℂ)

@[simp] lemma kernelCenterAction_mul_hom_app_f (g h : KillingExtension G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (((kernelCenterAction ω).mulIso g h).hom.app Z).f =
      (kernelTranslationMul ω g h).hom.app Z.1 := by
  exact DrinfeldEquivalence.centerAction_mul_hom_app_f (kernelAction ω) g h Z

end Paper18.Category.CrossedExtension
