import Paper18.Category.CrossedExtensionInnerNormalizationCochain
import Paper18.Category.CrossedExtensionActionMonoidal

/-! # Actual monoidal normalization of the kernel push functor -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Functor.LaxMonoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerNormalizationKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- Canonical push by conjugation, with the positive tensorator evaluated
at the original input degrees. The underlying regrading agrees with the
constructed action, while its tensorator uses the push convention. -/
def canonicalKernelPush (g : KillingExtension G) :
    CocycleVec (kernelCocycle ω) ⥤ CocycleVec (kernelCocycle ω) :=
  regradeFunctor ((conjugationAut g⁻¹).toAdditive)

instance canonicalKernelPush_additive (g : KillingExtension G) :
    (canonicalKernelPush ω g).Additive :=
  inferInstanceAs ((regradeFunctor ((conjugationAut g⁻¹).toAdditive)).Additive)

instance canonicalKernelPush_linear (g : KillingExtension G) :
    (canonicalKernelPush ω g).Linear ℂ :=
  inferInstanceAs ((regradeFunctor ((conjugationAut g⁻¹).toAdditive)).Linear ℂ)

instance canonicalKernelPush_isEquivalence (g : KillingExtension G) :
    (canonicalKernelPush ω g).IsEquivalence :=
  inferInstanceAs ((regradeEquivalence ((conjugationAut g⁻¹).toAdditive)).functor.IsEquivalence)

/-- The canonical push structure satisfies actual tensor associativity,
by the mixed pentagon for the actual primitive. -/
instance canonicalKernelPush_monoidal (g : KillingExtension G) :
    (canonicalKernelPush ω g).Monoidal :=
  scalarRegradeMonoidal
    (fun (a b c : Additive (KillingKernel G)) =>
      (kernelCocycle ω).val a.toMul b.toMul c.toMul)
    (fun (a b c d : Additive (KillingKernel G)) =>
      (kernelCocycle ω).pentagon a.toMul b.toMul c.toMul d.toMul)
    (fun (a c : Additive (KillingKernel G)) =>
      (kernelCocycle ω).one₂ a.toMul c.toMul)
    ((conjugationAut g⁻¹).toAdditive)
    (fun (a b : Additive (KillingKernel G)) =>
      conjugationTensorator ω g (conjugate g⁻¹ a.toMul) (conjugate g⁻¹ b.toMul))
    (fun (a b c : Additive (KillingKernel G)) => by
      simpa only [toMul_add, MulEquiv.toAdditive, conjugationAut, toMul_ofMul,
        conjugate_mul, conjugate_conjugate, mul_inv_cancel, conjugate_unit] using
        conjugationTensorator_coherence ω g (conjugate g⁻¹ a.toMul)
          (conjugate g⁻¹ b.toMul) (conjugate g⁻¹ c.toMul))
    (fun a => by simp)
    (fun a => by simp)

/-- The actual natural isomorphism multiplying each homogeneous fiber by
`θ(g,g⁻¹)`; the tensor equation is proved below. -/
def kernelPushNormalization (g : KillingExtension G) :
    kernelTranslation ω g ≅ canonicalKernelPush ω g :=
  pullbackScalarNatIso ((conjugationAut g⁻¹).toAdditive)
    ((conjugationAut g⁻¹).toAdditive) (fun _ => rfl)
    (fun a : Additive (KillingKernel G) => innerNormalization ω g a.toMul)

@[simp] lemma kernelPushNormalization_hom_app (g : KillingExtension G)
    (X : CocycleVec (kernelCocycle ω)) (a : Additive (KillingKernel G)) :
    (kernelPushNormalization ω g).hom.app X a =
      (innerNormalization ω g a.toMul : ℂ) • 𝟙 _ := rfl

@[simp] lemma canonicalKernelPush_tensorator (g : KillingExtension G)
    (X Y : CocycleVec (kernelCocycle ω)) :
    μ (canonicalKernelPush ω g) X Y =
      (weightedRegradeTensorIso ((conjugationAut g⁻¹).toAdditive)
        (fun a b : Additive (KillingKernel G) =>
          conjugationTensorator ω g (conjugate g⁻¹ a.toMul) (conjugate g⁻¹ b.toMul)) X Y).hom := rfl

/-- The comparison preserves the actual tensorators for arbitrary actual
graded vector spaces, rather than only for their degree labels. -/
theorem kernelPushNormalization_tensor (g : KillingExtension G)
    (X Y : CocycleVec (kernelCocycle ω)) :
    μ (kernelTranslation ω g) X Y ≫ (kernelPushNormalization ω g).hom.app (X ⊗ Y) =
      ((kernelPushNormalization ω g).hom.app X ⊗ₘ
        (kernelPushNormalization ω g).hom.app Y) ≫ μ (canonicalKernelPush ω g) X Y := by
  rw [kernelTranslation_tensorator, canonicalKernelPush_tensorator]
  exact weightedRegrade_comparison_tensor ((conjugationAut g⁻¹).toAdditive)
    ((conjugationAut g⁻¹).toAdditive) (fun _ => rfl) _ _ _
    (fun a b => innerNormalization_tensor ω g a.toMul b.toMul) X Y

instance kernelPushNormalization_monoidal (g : KillingExtension G) :
    NatTrans.IsMonoidal (kernelPushNormalization ω g).hom :=
  monoidalNatIso_isMonoidal_of_tensor (kernelPushNormalization ω g)
    (kernelPushNormalization_tensor ω g)

end Paper18.Category.CrossedExtension
