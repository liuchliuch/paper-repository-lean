import Paper18.Category.CrossedExtensionInnerCenterConjugationBraiding
import Paper18.Category.CrossedExtensionInnerCenterConjugationCoordinates
import Paper18.Category.CrossedExtensionInnerNormalizationCrossingTensor

/-! # The actual kernel-line conjugation diagram -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal Functor.OplaxMonoidal GradedObject.Monoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerConjugationDiagramFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The action tensorator and its actual multiplication comparisons carry
the canonical line crossing to the canonical crossing at the conjugated line. -/
theorem canonicalInnerCrossing_conjugation (g : KillingExtension G)
    (k : KillingKernel G) (X : CocycleVec (kernelCocycle ω)) :
    (kernelLineImageIso ω g k).inv ▷ (canonicalKernelPush ω g).obj X ≫
      μ (canonicalKernelPush ω g) (kernelLine ω k) X ≫
      (canonicalKernelPush ω g).map (canonicalInnerCrossing ω k X).hom ≫
      δ (canonicalKernelPush ω g) ((canonicalKernelPush ω k.val).obj X) (kernelLine ω k) ≫
      (canonicalKernelPushConjugationIso ω g k).hom.app X ▷
        (canonicalKernelPush ω g).obj (kernelLine ω k) ≫
      ((canonicalKernelPush ω (conjugate g k).val).obj ((canonicalKernelPush ω g).obj X)) ◁
        (kernelLineImageIso ω g k).hom =
      (canonicalInnerCrossing ω (conjugate g k) ((canonicalKernelPush ω g).obj X)).hom := by
  let H := canonicalKernelPush ω g
  let K := canonicalKernelPush ω k.val
  let N := kernelLine ω (conjugate g k)
  let L := kernelLine ω k
  let e := (conjugationAut g⁻¹).toAdditive
  let f := (conjugationAut k.val⁻¹).toAdditive
  apply GradedObject.hom_ext
  intro s
  apply tensorObj_ext (X₁ := N) (X₂ := H.obj X)
  intro i j h
  by_cases hi : i = Additive.ofMul (conjugate g k)
  · subst i
    obtain ⟨b, rfl⟩ := e.symm.surjective j
    obtain ⟨c, rfl⟩ := f.surjective b
    have heL : e (Additive.ofMul (conjugate g k)) = Additive.ofMul k := by
      change Additive.ofMul (conjugate g⁻¹ (conjugate g k)) = Additive.ofMul k
      simp
    have hb : Additive.ofMul k + f c = c + Additive.ofMul k := by
      exact canonicalInner_output_degree k c
    have hs : s = e.symm c + Additive.ofMul (conjugate g k) := by
      apply e.injective
      rw [← h, e.map_add, heL, e.apply_symm_apply, hb,
        e.map_add, e.apply_symm_apply, heL]
    rcases hs with rfl
    change ιTensorObj N (H.obj X) (Additive.ofMul (conjugate g k)) (e.symm (f c))
        (e.symm c + Additive.ofMul (conjugate g k)) h ≫
      (GradedObject.Monoidal.tensorHom (kernelLineImageIso ω g k).inv (𝟙 (H.obj X))
          (e.symm c + Additive.ofMul (conjugate g k)) ≫
        μ H L X (e.symm c + Additive.ofMul (conjugate g k)) ≫
        H.map (canonicalInnerCrossing ω k X).hom (e.symm c + Additive.ofMul (conjugate g k)) ≫
        δ H (K.obj X) L (e.symm c + Additive.ofMul (conjugate g k)) ≫
        GradedObject.Monoidal.tensorHom ((canonicalKernelPushConjugationIso ω g k).hom.app X)
          (𝟙 (H.obj L)) (e.symm c + Additive.ofMul (conjugate g k)) ≫
        GradedObject.Monoidal.tensorHom (𝟙 _)
          (kernelLineImageIso ω g k).hom (e.symm c + Additive.ofMul (conjugate g k))) =
      ιTensorObj N (H.obj X) (Additive.ofMul (conjugate g k)) (e.symm (f c))
        (e.symm c + Additive.ofMul (conjugate g k)) h ≫
        (canonicalInnerCrossing ω (conjugate g k) (H.obj X)).hom
          (e.symm c + Additive.ofMul (conjugate g k))
    rw [ι_tensorHom_assoc]
    have hδ : δ H (K.obj X) L =
        (weightedRegradeTensorIso e
          (fun a b : Additive (KillingKernel G) =>
            conjugationTensorator ω g (conjugate g⁻¹ a.toMul) (conjugate g⁻¹ b.toMul))
          (K.obj X) L).inv := rfl
    rw [canonicalKernelPush_tensorator, hδ]
    dsimp only [H, canonicalKernelPush]
    have hμ := inclusion_weightedRegradeTensorIso e
      (fun a b : Additive (KillingKernel G) =>
        conjugationTensorator ω g (conjugate g⁻¹ a.toMul) (conjugate g⁻¹ b.toMul))
      L X (Additive.ofMul (conjugate g k)) (e.symm (f c))
      (e.symm c + Additive.ofMul (conjugate g k)) h
    rw [reassoc_of% hμ]
    have hm : (regradeFunctor e).map (canonicalInnerCrossing ω k X).hom
        (e.symm c + Additive.ofMul (conjugate g k)) =
      (canonicalInnerCrossing ω k X).hom
        (e (e.symm c + Additive.ofMul (conjugate g k))) := rfl
    rw [hm]
    have hj : e (e.symm (f c)) =
        Additive.ofMul (conjugate k.val⁻¹ (e (e.symm c)).toMul) := by
      change e (e.symm (f c)) = f (e (e.symm c))
      simp only [e.apply_symm_apply]
    have hγ := inclusion_canonicalInnerCrossing_transport ω k X
      (e (Additive.ofMul (conjugate g k))) (e (e.symm (f c))) (e (e.symm c))
      (e (e.symm c + Additive.ofMul (conjugate g k))) heL hj
      (by rw [← e.map_add, h]) (e.map_add _ _).symm
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
    rw [reassoc_of% hγ]
    have hδi := inclusion_weightedRegradeTensorIso_inv e
      (fun a b : Additive (KillingKernel G) =>
        conjugationTensorator ω g (conjugate g⁻¹ a.toMul) (conjugate g⁻¹ b.toMul))
      (K.obj X) L (e.symm c) (Additive.ofMul (conjugate g k))
      (e.symm c + Additive.ofMul (conjugate g k)) rfl
    rw [reassoc_of% hδi]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc]
    dsimp only [K, canonicalKernelPush]
    rw [ι_tensorHom_assoc, ι_tensorHom]
    simp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id,
      MonoidalCategory.tensorHom_id, MonoidalCategory.id_tensorHom, Category.assoc]
    have hesym (z : Additive (KillingKernel G)) :
        e.symm z = Additive.ofMul (conjugate g z.toMul) := by
      change Additive.ofMul (conjugate (g⁻¹)⁻¹ z.toMul) = _
      rw [inv_inv]
    have hjN : e.symm (f c) = Additive.ofMul
        (conjugate (conjugate g k).val⁻¹ (e.symm c).toMul) := by
      simp only [hesym]
      apply Additive.toMul.injective
      apply Subtype.ext
      change g * (k.val⁻¹ * c.toMul.val * (k.val⁻¹)⁻¹) * g⁻¹ =
        (g * k.val * g⁻¹)⁻¹ * (g * c.toMul.val * g⁻¹) * ((g * k.val * g⁻¹)⁻¹)⁻¹
      group
    have hγN := inclusion_canonicalInnerCrossing_transport ω (conjugate g k) (H.obj X)
      (Additive.ofMul (conjugate g k)) (e.symm (f c)) (e.symm c)
      (e.symm c + Additive.ofMul (conjugate g k)) rfl hjN h rfl
    dsimp only [H, canonicalKernelPush] at hγN
    rw [hγN, canonicalKernelPushConjugationIso_hom_app]
    let R := (GradedObject.eval (Additive.ofMul (conjugate g k))).mapIso
      (kernelLineImageIso ω g k)
    let q₁ := congrArg X hj
    let q₂ := congrArg X (canonicalConjugation_degree g k (e.symm c))
    let q₃ := congrArg (H.obj X) hjN
    let c₀ : ℂ := (conjugationTensorator ω g
      (conjugate g⁻¹ (Additive.ofMul (conjugate g k)).toMul)
      (conjugate g⁻¹ (e.symm (f c)).toMul) : ℂˣ)
    let c₁ : ℂ := ((conjugationTensorator ω g
      (conjugate g⁻¹ (e.symm c).toMul)
      (conjugate g⁻¹ (Additive.ofMul (conjugate g k)).toMul) : ℂˣ) : ℂ)⁻¹
    let c₂ : ℂ := ((conjugationComparison ω g k.val
      (conjugate (g * k.val)⁻¹ (e.symm c).toMul))⁻¹ *
        conjugationComparison ω (conjugate g k).val g
          (conjugate (g * k.val)⁻¹ (e.symm c).toMul) : ℂˣ)
    let P := ιTensorObj ((canonicalKernelPush ω (conjugate g k).val).obj (H.obj X))
      N (e.symm c) (Additive.ofMul (conjugate g k))
        (e.symm c + Additive.ofMul (conjugate g k)) rfl
    let U : FGModuleCat ℂ := (H.obj L) (Additive.ofMul (conjugate g k))
    let V : FGModuleCat ℂ := N (Additive.ofMul (conjugate g k))
    let Q : FGModuleCat ℂ := (H.obj X) (e.symm (f c))
    let T : FGModuleCat ℂ :=
      ((canonicalKernelPush ω (conjugate g k).val).obj (H.obj X)) (e.symm c)
    have hiL : (𝟙 ((regradeFunctor e).obj L)) (Additive.ofMul (conjugate g k)) =
        𝟙 U := rfl
    have hiX : (𝟙 ((regradeFunctor e).obj X)) (e.symm (f c)) = 𝟙 Q := rfl
    rw [hiL, hiX]
    have ht : ((c₂ • eqToHom q₂) ⊗ₘ 𝟙 U) = c₂ • (eqToHom q₂ ▷ U) := by
      rw [MonoidalCategory.tensorHom_id, MonoidalLinear.smul_whiskerRight]
    rw [ht]
    simp only [Linear.comp_smul, Linear.smul_comp, Category.assoc, smul_smul]
    have hscal : c₀ * (c₁ * c₂) = 1 := by
      simpa only [c₀, c₁, c₂, Units.val_mul, Units.val_one,
        Units.val_inv_eq_inv_val, mul_assoc] using
        congrArg (fun z : ℂˣ => (z : ℂ)) (innerConjugation_scalar_regrade ω g k c)
    simp only [Units.val_inv_eq_inv_val]
    rw [hscal, one_smul]
    have hbraid := lineBraiding_eqToHom R q₁ q₂ q₃
    simpa only [Category.assoc] using congrArg (fun z => z ≫ P) hbraid
  · exact ((tensorRight ((H.obj X) j)).map_isZero
      (simpleFiber_isZero _ _ _ hi)).eq_of_src _ _

end Paper18.Category.CrossedExtension
