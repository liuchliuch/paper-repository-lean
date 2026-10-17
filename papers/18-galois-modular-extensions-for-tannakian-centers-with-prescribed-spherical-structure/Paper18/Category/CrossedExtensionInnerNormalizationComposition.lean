import Paper18.Category.CrossedExtensionInnerNormalization

/-! # Actual multiplication comparison for canonical push conjugation -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Functor.LaxMonoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCompositionKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The canonical push multiplication scalar satisfies the actual tensor
comparison equation, by the actual six-mixed-pentagon identity. -/
theorem canonicalPushComparison_tensor (g h : KillingExtension G) (k l : KillingKernel G) :
    conjugationTensorator ω g (conjugate g⁻¹ k) (conjugate g⁻¹ l) *
        conjugationTensorator ω h (conjugate (g * h)⁻¹ k) (conjugate (g * h)⁻¹ l) *
        (conjugationComparison ω g h (conjugate (g * h)⁻¹ (k * l)))⁻¹ =
      (conjugationComparison ω g h (conjugate (g * h)⁻¹ k))⁻¹ *
        (conjugationComparison ω g h (conjugate (g * h)⁻¹ l))⁻¹ *
        conjugationTensorator ω (g * h) (conjugate (g * h)⁻¹ k) (conjugate (g * h)⁻¹ l) := by
  have he : ∀ a : KillingKernel G, conjugate h (conjugate (g * h)⁻¹ a) = conjugate g⁻¹ a := by
    intro a
    rw [conjugate_conjugate]
    congr 1
    group
  have e := congrArg Additive.ofMul
    (conjugationComparison_tensor ω g h (conjugate (g * h)⁻¹ k) (conjugate (g * h)⁻¹ l))
  simp only [he, ← conjugate_mul, ofMul_mul] at e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  linear_combination (norm := abel) -e

/-- Actual multiplication natural isomorphism in the canonical push
convention, including the actual transports between equal fibers. -/
def canonicalKernelPushMul (g h : KillingExtension G) :
    canonicalKernelPush ω h ⋙ canonicalKernelPush ω g ≅ canonicalKernelPush ω (g * h) :=
  pullbackScalarNatIso
    (fun a : Additive (KillingKernel G) =>
      Additive.ofMul (conjugate h⁻¹ (conjugate g⁻¹ a.toMul)))
    (fun a : Additive (KillingKernel G) => Additive.ofMul (conjugate (g * h)⁻¹ a.toMul))
    (fun a => by simp only [conjugate_conjugate, mul_inv_rev])
    (fun a => (conjugationComparison ω g h (conjugate (g * h)⁻¹ a.toMul))⁻¹)

@[simp] lemma canonicalKernelPushMul_hom_app (g h : KillingExtension G)
    (X : CocycleVec (kernelCocycle ω)) (a : Additive (KillingKernel G)) :
    (canonicalKernelPushMul ω g h).hom.app X a =
      ((conjugationComparison ω g h (conjugate (g * h)⁻¹ a.toMul))⁻¹ : ℂˣ).val •
        eqToHom (congrArg X (show
          Additive.ofMul (conjugate h⁻¹ (conjugate g⁻¹ a.toMul)) =
          Additive.ofMul (conjugate (g * h)⁻¹ a.toMul) by
            simp only [conjugate_conjugate, mul_inv_rev])) := rfl

/-- The natural normalization intertwines the actual action multiplication
with the canonical push multiplication, on every actual object. -/
theorem kernelPushNormalization_comp (g h : KillingExtension G)
    (X : CocycleVec (kernelCocycle ω)) :
    (kernelTranslationMul ω g h).hom.app X ≫ (kernelPushNormalization ω (g * h)).hom.app X =
      (kernelTranslation ω g).map ((kernelPushNormalization ω h).hom.app X) ≫
        (kernelPushNormalization ω g).hom.app ((canonicalKernelPush ω h).obj X) ≫
          (canonicalKernelPushMul ω g h).hom.app X := by
  apply GradedObject.hom_ext
  intro a
  change (kernelTranslationMul ω g h).hom.app X a ≫
      (kernelPushNormalization ω (g * h)).hom.app X a =
    (kernelTranslation ω g).map ((kernelPushNormalization ω h).hom.app X) a ≫
      (kernelPushNormalization ω g).hom.app ((canonicalKernelPush ω h).obj X) a ≫
        (canonicalKernelPushMul ω g h).hom.app X a
  rw [kernelTranslationMul_hom_app, kernelPushNormalization_hom_app,
    kernelTranslation_map_apply, kernelPushNormalization_hom_app,
    kernelPushNormalization_hom_app, canonicalKernelPushMul_hom_app]
  simp only [Linear.smul_comp, Linear.comp_smul, comp_id, id_comp, smul_smul]
  congr 1
  have e := congrArg (fun z : ℂˣ => (z : ℂ)) (innerNormalization_comp ω g h a.toMul)
  simpa only [Units.val_mul, mul_comm, mul_left_comm, mul_assoc] using e

/-- Actual monoidal tensor square of the canonical push multiplication. -/
theorem canonicalKernelPushMul_tensor (g h : KillingExtension G)
    (X Y : CocycleVec (kernelCocycle ω)) :
    μ (canonicalKernelPush ω h ⋙ canonicalKernelPush ω g) X Y ≫
        (canonicalKernelPushMul ω g h).hom.app (X ⊗ Y) =
      ((canonicalKernelPushMul ω g h).hom.app X ⊗ₘ
        (canonicalKernelPushMul ω g h).hom.app Y) ≫ μ (canonicalKernelPush ω (g * h)) X Y := by
  rw [Functor.LaxMonoidal.comp_μ, canonicalKernelPush_tensorator,
    canonicalKernelPush_tensorator, canonicalKernelPush_tensorator]
  dsimp only [canonicalKernelPush]
  rw [weightedRegrade_comp_tensor]
  let e := (conjugationAut g⁻¹).toAdditive
  let f := (conjugationAut h⁻¹).toAdditive
  let d := (conjugationAut (g * h)⁻¹).toAdditive
  let t := fun a b : Additive (KillingKernel G) =>
    conjugationTensorator ω g (conjugate g⁻¹ a.toMul) (conjugate g⁻¹ b.toMul) *
      conjugationTensorator ω h (conjugate h⁻¹ (e a).toMul) (conjugate h⁻¹ (e b).toMul)
  let u := fun a b : Additive (KillingKernel G) =>
    conjugationTensorator ω (g * h) (conjugate (g * h)⁻¹ a.toMul) (conjugate (g * h)⁻¹ b.toMul)
  let s := fun a : Additive (KillingKernel G) =>
    (conjugationComparison ω g h (conjugate (g * h)⁻¹ a.toMul))⁻¹
  have he (a : Additive (KillingKernel G)) : (e.trans f) a = d a := by
    change Additive.ofMul (conjugate h⁻¹ (conjugate g⁻¹ a.toMul)) =
      Additive.ofMul (conjugate (g * h)⁻¹ a.toMul)
    simp only [conjugate_conjugate, mul_inv_rev]
  have hs (a b : Additive (KillingKernel G)) : t a b * s (a + b) = s a * s b * u a b := by
    change conjugationTensorator ω g (conjugate g⁻¹ a.toMul) (conjugate g⁻¹ b.toMul) *
        conjugationTensorator ω h (conjugate h⁻¹ (conjugate g⁻¹ a.toMul))
          (conjugate h⁻¹ (conjugate g⁻¹ b.toMul)) *
        (conjugationComparison ω g h (conjugate (g * h)⁻¹ (a.toMul * b.toMul)))⁻¹ =
      (conjugationComparison ω g h (conjugate (g * h)⁻¹ a.toMul))⁻¹ *
        (conjugationComparison ω g h (conjugate (g * h)⁻¹ b.toMul))⁻¹ *
        conjugationTensorator ω (g * h) (conjugate (g * h)⁻¹ a.toMul)
          (conjugate (g * h)⁻¹ b.toMul)
    simpa only [conjugate_conjugate, mul_inv_rev] using
      canonicalPushComparison_tensor ω g h a.toMul b.toMul
  exact weightedRegrade_comparison_tensor (e.trans f) d he t u s hs X Y

instance canonicalKernelPushMul_monoidal (g h : KillingExtension G) :
    NatTrans.IsMonoidal (canonicalKernelPushMul ω g h).hom :=
  monoidalNatIso_isMonoidal_of_tensor (canonicalKernelPushMul ω g h)
    (canonicalKernelPushMul_tensor ω g h)

end Paper18.Category.CrossedExtension
