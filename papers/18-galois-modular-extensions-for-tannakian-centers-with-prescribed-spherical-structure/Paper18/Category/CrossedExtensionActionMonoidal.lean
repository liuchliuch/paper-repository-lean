import Paper18.Category.CrossedExtensionActionTensor
import Paper18.Category.MonoidalNatIsoUnit
import Paper18.Category.EquivariantMonoidal

/-! # The actual coherent strong monoidal kernel conjugation action -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance actionMonoidalKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

instance kernelAction_rho_additive (g : KillingExtension G) :
    ((kernelAction ω).ρ g).Additive := kernelConjugationFunctor_additive ω g⁻¹

instance kernelAction_rho_linear (g : KillingExtension G) :
    ((kernelAction ω).ρ g).Linear ℂ := kernelConjugationFunctor_linear ω g⁻¹

/-- All multiplication and unit comparisons of the constructed actual
conjugation action are monoidal. The unit squares are derived from the
proved tensor squares and actual invertibility. -/
instance kernelAction_isMonoidal : (kernelAction ω).IsMonoidal where
  unit_monoidal := monoidalNatIso_isMonoidal_of_tensor (kernelAction ω).unitIso
    (kernelTranslationUnit_tensor ω)
  mul_monoidal g h := monoidalNatIso_isMonoidal_of_tensor ((kernelAction ω).mulIso g h)
    (kernelTranslationMul_tensor ω g h)

end Paper18.Category.CrossedExtension
