import Paper18.Category.CrossedExtensionAction
import Paper18.Category.CrossedExtensionScalarComparison

/-! # Actual tensor squares for the kernel conjugation action -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.MonoidalCategory Functor.LaxMonoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance actionTensorKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _
local instance actionTensorTranslationMonoidal (g : KillingExtension G) :
    (kernelTranslation ω g).Monoidal := kernelTranslation_monoidal ω g

@[simp] lemma kernelTranslation_tensorator (g : KillingExtension G)
    (X Y : CocycleVec (kernelCocycle ω)) :
    μ (kernelTranslation ω g) X Y =
      (weightedRegradeTensorIso ((conjugationAut g⁻¹).toAdditive)
        (fun a b : Additive (KillingKernel G) =>
          (conjugationTensorator ω g⁻¹ a.toMul b.toMul)⁻¹) X Y).hom := rfl

/-- The actual unit natural isomorphism preserves actual tensorators. -/
theorem kernelTranslationUnit_tensor (X Y : CocycleVec (kernelCocycle ω)) :
    μ (kernelTranslation ω 1) X Y ≫ (kernelTranslationUnit ω).hom.app (X ⊗ Y) =
      ((kernelTranslationUnit ω).hom.app X ⊗ₘ (kernelTranslationUnit ω).hom.app Y) ≫
        μ (𝟭 (CocycleVec (kernelCocycle ω))) X Y := by
  rw [kernelTranslation_tensorator]
  let e := (conjugationAut (1 : KillingExtension G)⁻¹).toAdditive
  let t := fun a b : Additive (KillingKernel G) =>
    (conjugationTensorator ω (1 : KillingExtension G)⁻¹ a.toMul b.toMul)⁻¹
  have he (a : Additive (KillingKernel G)) : e a = (AddEquiv.refl _) a := by
    change Additive.ofMul (conjugate (1 : KillingExtension G)⁻¹ a.toMul) = a
    simp
  have ht (a b : Additive (KillingKernel G)) : t a b = 1 := by
    simp only [t, inv_one, conjugationTensorator_unit]
  have hh := weightedRegrade_comparison_tensor e (AddEquiv.refl _) he t
    (fun _ _ => 1) (fun _ => 1) (fun a b => by rw [ht]; simp) X Y
  rw [weightedRegrade_identity_tensor] at hh
  exact hh

/-- The actual multiplication natural isomorphisms preserve actual
tensorators, using the proved six-pentagon scalar identity. -/
theorem kernelTranslationMul_tensor (g h : KillingExtension G)
    (X Y : CocycleVec (kernelCocycle ω)) :
    μ (kernelTranslation ω h ⋙ kernelTranslation ω g) X Y ≫
        (kernelTranslationMul ω g h).hom.app (X ⊗ Y) =
      ((kernelTranslationMul ω g h).hom.app X ⊗ₘ
        (kernelTranslationMul ω g h).hom.app Y) ≫ μ (kernelTranslation ω (g * h)) X Y := by
  rw [Functor.LaxMonoidal.comp_μ, kernelTranslation_tensorator,
    kernelTranslation_tensorator, kernelTranslation_tensorator]
  dsimp only [kernelTranslation, kernelConjugationFunctor]
  rw [weightedRegrade_comp_tensor]
  let e := (conjugationAut g⁻¹).toAdditive
  let f := (conjugationAut h⁻¹).toAdditive
  let d := (conjugationAut (g * h)⁻¹).toAdditive
  let t := fun a b : Additive (KillingKernel G) =>
    (conjugationTensorator ω g⁻¹ a.toMul b.toMul)⁻¹ *
      (conjugationTensorator ω h⁻¹ (e a).toMul (e b).toMul)⁻¹
  let u := fun a b : Additive (KillingKernel G) =>
    (conjugationTensorator ω (g * h)⁻¹ a.toMul b.toMul)⁻¹
  let s := fun a : Additive (KillingKernel G) => conjugationComparison ω h⁻¹ g⁻¹ a.toMul
  have he (a : Additive (KillingKernel G)) : (e.trans f) a = d a := by
    change Additive.ofMul (conjugate h⁻¹ (conjugate g⁻¹ a.toMul)) =
      Additive.ofMul (conjugate (g * h)⁻¹ a.toMul)
    simp only [conjugate_conjugate, mul_inv_rev]
  have hs (a b : Additive (KillingKernel G)) : t a b * s (a + b) = s a * s b * u a b := by
    simpa only [t, u, s, mul_inv_rev] using
      conjugationComparison_tensor_pullback ω h⁻¹ g⁻¹ a.toMul b.toMul
  exact weightedRegrade_comparison_tensor (e.trans f) d he t u s hs X Y

end Paper18.Category.CrossedExtension
