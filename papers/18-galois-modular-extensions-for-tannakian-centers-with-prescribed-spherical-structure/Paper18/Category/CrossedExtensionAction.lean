import Paper18.Category.CrossedExtensionScalarAction

/-! # The actual weak conjugation action of the finite killing extension -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance actionKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- Actual weak action on all kernel-graded vector spaces. Every action
coherence follows from the proved degree and actual primitive equations. -/
def kernelAction : WeakAction (KillingExtension G) (CocycleVec (kernelCocycle ω)) :=
  scalarPullbackAction
    (fun g (a : Additive (KillingKernel G)) => Additive.ofMul (conjugate g⁻¹ a.toMul))
    (fun a => by simp)
    (fun g h a => by simp only [toMul_ofMul, conjugate_conjugate, mul_inv_rev])
    (fun g h a => conjugationComparison ω h⁻¹ g⁻¹ a.toMul)
    (fun g a => by simp)
    (fun g a => by simp)
    (fun g h j a => by
      simpa only [mul_inv_rev] using
        conjugationComparison_assoc ω j⁻¹ h⁻¹ g⁻¹ a.toMul)

instance kernelAction_rho_monoidal (g : KillingExtension G) :
    ((kernelAction ω).ρ g).Monoidal := kernelTranslation_monoidal ω g

end Paper18.Category.CrossedExtension
