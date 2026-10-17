import Paper18.Category.CrossedExtensionInnerCenterConjugationBasic

/-! # Actual conjugation comparison between canonical push functors -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCenterConjugationFunctorFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The two actual composite pullbacks in the conjugation square have
the same source degree. -/
lemma canonicalConjugation_degree (g : KillingExtension G) (k : KillingKernel G)
    (a : Additive (KillingKernel G)) :
    Additive.ofMul (conjugate k.val⁻¹ (conjugate g⁻¹ a.toMul)) =
      Additive.ofMul (conjugate g⁻¹ (conjugate (conjugate g k).val⁻¹ a.toMul)) := by
  rw [conjugate_conjugate, conjugate_conjugate]
  congr 1
  simp only [conjugate_val, mul_inv_rev, inv_inv]
  group

/-- The actual natural comparison from `H_g H_k` to `H_(gkg⁻¹) H_g`.
Its coefficient is the ratio of the two constructed multiplication
comparisons, rather than an independently supplied coherence datum. -/
def canonicalKernelPushConjugationIso (g : KillingExtension G) (k : KillingKernel G) :
    canonicalKernelPush ω k.val ⋙ canonicalKernelPush ω g ≅
      canonicalKernelPush ω g ⋙ canonicalKernelPush ω (conjugate g k).val :=
  pullbackScalarNatIso
    (fun a : Additive (KillingKernel G) =>
      Additive.ofMul (conjugate k.val⁻¹ (conjugate g⁻¹ a.toMul)))
    (fun a : Additive (KillingKernel G) =>
      Additive.ofMul (conjugate g⁻¹ (conjugate (conjugate g k).val⁻¹ a.toMul)))
    (canonicalConjugation_degree g k)
    (fun a => (conjugationComparison ω g k.val (conjugate (g * k.val)⁻¹ a.toMul))⁻¹ *
      conjugationComparison ω (conjugate g k).val g (conjugate (g * k.val)⁻¹ a.toMul))

@[simp] lemma canonicalKernelPushConjugationIso_hom_app (g : KillingExtension G)
    (k : KillingKernel G) (X : CocycleVec (kernelCocycle ω))
    (a : Additive (KillingKernel G)) :
    (canonicalKernelPushConjugationIso ω g k).hom.app X a =
      (((conjugationComparison ω g k.val (conjugate (g * k.val)⁻¹ a.toMul))⁻¹ *
        conjugationComparison ω (conjugate g k).val g
          (conjugate (g * k.val)⁻¹ a.toMul) : ℂˣ) : ℂ) •
        eqToHom (congrArg X (canonicalConjugation_degree g k a)) := rfl

end Paper18.Category.CrossedExtension
