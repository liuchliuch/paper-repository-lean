import Paper18.Category.CrossedExtensionInnerNormalizationCrossingTensor

/-! # Actual tensor hexagon of the canonical kernel-line crossing -/
noncomputable section
set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal GradedObject.Monoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerHexagonKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The actual canonical line crossing obeys the tensor hexagon with the
actual push tensorator. -/
theorem canonicalInnerCrossing_tensor_forward (k : KillingKernel G)
    (X Y : CocycleVec (kernelCocycle ω)) :
    (α_ (kernelLine ω k) X Y).hom ≫
        (canonicalInnerCrossing ω k (X ⊗ Y)).hom =
      (canonicalInnerCrossing ω k X).hom ▷ Y ≫
        (α_ ((canonicalKernelPush ω k.val).obj X)
          (kernelLine ω k) Y).hom ≫
        ((canonicalKernelPush ω k.val).obj X) ◁ (canonicalInnerCrossing ω k Y).hom ≫
        (α_ ((canonicalKernelPush ω k.val).obj X) ((canonicalKernelPush ω k.val).obj Y)
          (kernelLine ω k)).inv ≫
        μ (canonicalKernelPush ω k.val) X Y ▷
          kernelLine ω k := by
  have hTensor (U V : CocycleVec (kernelCocycle ω)) : U ⊗ V = GradedObject.Monoidal.tensorObj U V := rfl
  let L := kernelLine ω k
  let H := canonicalKernelPush ω k.val
  let e := (conjugationAut k.val⁻¹).toAdditive
  have hdeg (c : Additive (KillingKernel G)) : Additive.ofMul k + e c = c + Additive.ofMul k :=
    canonicalInner_output_degree k c
  let r := fun a b c : Additive (KillingKernel G) => (kernelCocycle ω).val a.toMul b.toMul c.toMul
  have hγ (T : CocycleVec (kernelCocycle ω)) (c : Additive (KillingKernel G)) :
      ιTensorObj L T (Additive.ofMul k) (e c) (c + Additive.ofMul k)
          (canonicalInner_output_degree k c) ≫
          (canonicalInnerCrossing ω k T).hom (c + Additive.ofMul k) =
        (β_ (L (Additive.ofMul k)) ((H.obj T) c)).hom ≫
          ιTensorObj (H.obj T) L c (Additive.ofMul k) (c + Additive.ofMul k) rfl :=
    inclusion_canonicalInnerCrossing_output ω k T c
  apply GradedObject.hom_ext
  intro s
  apply tensorObj₃'_ext (X₁ := L) (X₂ := X) (X₃ := Y)
  intro i a b h
  by_cases hi : i = Additive.ofMul k
  · subst i
    obtain ⟨a, rfl⟩ := e.surjective a
    obtain ⟨b, rfl⟩ := e.surjective b
    have hd : Additive.ofMul k + e a + e b = a + b + Additive.ofMul k := by
      change Additive.ofMul k + Additive.ofMul (conjugate k.val⁻¹ a.toMul) +
        Additive.ofMul (conjugate k.val⁻¹ b.toMul) = _
      rw [canonicalInner_output_degree, add_assoc, canonicalInner_output_degree, ← add_assoc]
    have hs : s = a + b + Additive.ofMul k := h.symm.trans hd
    subst hs
    change ιTensorObj₃' L X Y (Additive.ofMul k) (e a) (e b)
        (a + b + Additive.ofMul k) h ≫
        ((scalarAssociator r L X Y).hom (a + b + Additive.ofMul k) ≫
          (canonicalInnerCrossing ω k (X ⊗ Y)).hom (a + b + Additive.ofMul k)) =
      ιTensorObj₃' L X Y (Additive.ofMul k) (e a) (e b)
        (a + b + Additive.ofMul k) h ≫
        (GradedObject.Monoidal.whiskerRight (canonicalInnerCrossing ω k X).hom Y
            (a + b + Additive.ofMul k) ≫
          (scalarAssociator r (H.obj X) L Y).hom (a + b + Additive.ofMul k) ≫
          GradedObject.Monoidal.whiskerLeft (H.obj X) (canonicalInnerCrossing ω k Y).hom
            (a + b + Additive.ofMul k) ≫
          (scalarAssociator r (H.obj X) (H.obj Y) L).inv (a + b + Additive.ofMul k) ≫
          GradedObject.Monoidal.whiskerRight (μ H X Y) L (a + b + Additive.ofMul k))
    dsimp only [CocycleVec.instMonoidalCategory, twistedMonoidalCategory, scalarMonoidalCategory,
      PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
    have hXY :
        ιTensorObj L (GradedObject.Monoidal.tensorObj X Y) (Additive.ofMul k)
          (e (a + b)) (a + b + Additive.ofMul k) (canonicalInner_output_degree k (a + b)) ≫
          (canonicalInnerCrossing ω k (X ⊗ Y)).hom (a + b + Additive.ofMul k) =
        (β_ (L (Additive.ofMul k)) (H.obj (X ⊗ Y) (a + b))).hom ≫
          ιTensorObj (H.obj (X ⊗ Y)) L (a + b) (Additive.ofMul k)
            (a + b + Additive.ofMul k) rfl := hγ (X ⊗ Y) (a + b)
    have hμi :
        ιTensorObj (H.obj X) (H.obj Y) a b (a + b) rfl ≫ (μ H X Y) (a + b) =
          (conjugationTensorator ω k.val (e a).toMul (e b).toMul : ℂ) •
            ιTensorObj X Y (e a) (e b) (e (a + b)) (e.map_add a b).symm := by
      exact inclusion_weightedRegradeTensorIso e
        (fun c d => conjugationTensorator ω k.val (e c).toMul (e d).toMul)
        X Y a b (a + b) rfl
    conv_lhs =>
      rw [inclusion_scalarAssociator_assoc]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
      rw [ιTensorObj₃_eq L X Y (Additive.ofMul k) (e a) (e b)
        (a + b + Additive.ofMul k) h (e (a + b)) (e.map_add a b).symm,
        Category.assoc]
      simp only [Category.assoc]
      tactic =>
        exact congrArg (fun f => (r (Additive.ofMul k) (e a) (e b) : ℂ) •
          ((α_ (L (Additive.ofMul k)) (X (e a)) (Y (e b))).hom ≫
            L (Additive.ofMul k) ◁ ιTensorObj X Y (e a) (e b) (e (a + b)) (e.map_add a b).symm ≫ f)) hXY
    dsimp only
    have hn : L (Additive.ofMul k) ◁
        ιTensorObj X Y (e a) (e b) (e (a + b)) (e.map_add a b).symm ≫
          (β_ (L (Additive.ofMul k)) (H.obj (X ⊗ Y) (a + b))).hom =
        (β_ (L (Additive.ofMul k)) (X (e a) ⊗ Y (e b))).hom ≫
          ιTensorObj X Y (e a) (e b) (e (a + b)) (e.map_add a b).symm ▷ L (Additive.ofMul k) :=
      BraidedCategory.braiding_naturality_right _ _
    have hLN := congrArg (fun f => (r (Additive.ofMul k) (e a) (e b) : ℂ) •
      ((α_ (L (Additive.ofMul k)) (X (e a)) (Y (e b))).hom ≫ f ≫
        ιTensorObj (H.obj (X ⊗ Y)) L (a + b) (Additive.ofMul k)
          (a + b + Additive.ofMul k) rfl)) hn
    dsimp only at hLN
    simp only [Category.assoc] at hLN
    conv_lhs => tactic => exact hLN
    conv_rhs =>
      rw [ιTensorObj₃'_eq L X Y (Additive.ofMul k) (e a) (e b)
        (a + b + Additive.ofMul k) h (a + Additive.ofMul k) (canonicalInner_output_degree k a),
        Category.assoc, ι_tensorHom_assoc]
      dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
      rw [MonoidalCategory.tensorHom_id, ← MonoidalCategory.comp_whiskerRight_assoc]
      simp only [Category.assoc]
      rw [hγ X a]
      dsimp only [CocycleVec.instMonoidalCategory, twistedMonoidalCategory, scalarMonoidalCategory,
        PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
      simp only [comp_whiskerRight, Category.assoc, hTensor]
      change (β_ (L (Additive.ofMul k)) (H.obj X a)).hom ▷ Y (e b) ≫
        ιTensorObj (H.obj X) L a (Additive.ofMul k) (a + Additive.ofMul k) rfl ▷ Y (e b) ≫
          ιTensorObj (GradedObject.Monoidal.tensorObj (H.obj X) L) Y
            (a + Additive.ofMul k) (e b) (a + b + Additive.ofMul k)
            (by rw [add_assoc, hdeg b, ← add_assoc]) ≫
          (scalarAssociator r (H.obj X) L Y).hom (a + b + Additive.ofMul k) ≫
          GradedObject.Monoidal.whiskerLeft (H.obj X) (canonicalInnerCrossing ω k Y).hom
            (a + b + Additive.ofMul k) ≫
          (scalarAssociator r (H.obj X) (H.obj Y) L).inv (a + b + Additive.ofMul k) ≫
          GradedObject.Monoidal.whiskerRight (μ H X Y) L (a + b + Additive.ofMul k)
      rw [← ιTensorObj₃'_eq_assoc (H.obj X) L Y a (Additive.ofMul k) (e b)
        (a + b + Additive.ofMul k) (by rw [add_assoc, hdeg b, ← add_assoc])
        (a + Additive.ofMul k) rfl, inclusion_scalarAssociator_assoc]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
      rw [ιTensorObj₃_eq (H.obj X) L Y a (Additive.ofMul k) (e b)
        (a + b + Additive.ofMul k) (by rw [add_assoc, hdeg b, ← add_assoc])
        (b + Additive.ofMul k) (canonicalInner_output_degree k b),
        Category.assoc, ι_tensorHom_assoc]
      dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
      rw [MonoidalCategory.id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc]
      simp only [Category.assoc]
      rw [hγ Y b]
      dsimp only [CocycleVec.instMonoidalCategory, twistedMonoidalCategory, scalarMonoidalCategory,
        PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
      simp only [whiskerLeft_comp, Category.assoc, hTensor]
      change (r a (Additive.ofMul k) (e b) : ℂ) •
        ((β_ (L (Additive.ofMul k)) (H.obj X a)).hom ▷ Y (e b) ≫
          (α_ (H.obj X a) (L (Additive.ofMul k)) (Y (e b))).hom ≫
          H.obj X a ◁ (β_ (L (Additive.ofMul k)) (H.obj Y b)).hom ≫
          H.obj X a ◁ ιTensorObj (H.obj Y) L b (Additive.ofMul k) (b + Additive.ofMul k) rfl ≫
          ιTensorObj (H.obj X) (GradedObject.Monoidal.tensorObj (H.obj Y) L)
            a (b + Additive.ofMul k) (a + b + Additive.ofMul k) (add_assoc _ _ _).symm ≫
          (scalarAssociator r (H.obj X) (H.obj Y) L).inv (a + b + Additive.ofMul k) ≫
          GradedObject.Monoidal.whiskerRight (μ H X Y) L (a + b + Additive.ofMul k))
      rw [← ιTensorObj₃_eq_assoc (H.obj X) (H.obj Y) L a b (Additive.ofMul k)
        (a + b + Additive.ofMul k) rfl (b + Additive.ofMul k) rfl,
        inclusion_scalarAssociator_inv_assoc]
      simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
      rw [ιTensorObj₃'_eq (H.obj X) (H.obj Y) L a b (Additive.ofMul k)
        (a + b + Additive.ofMul k) rfl (a + b) rfl, Category.assoc, ι_tensorHom]
      dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
      rw [MonoidalCategory.tensorHom_id, ← MonoidalCategory.comp_whiskerRight_assoc]
      rw [hμi]
      simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul,
        Category.assoc, smul_smul]
    have he (c : Additive (KillingKernel G)) :
        conjugate k.val (e c).toMul = c.toMul := by
      change conjugate k.val (conjugate k.val⁻¹ c.toMul) = _
      rw [conjugate_conjugate, mul_inv_cancel, conjugate_unit]
    have hc := canonicalInnerCrossing_scalar ω k (e a).toMul (e b).toMul
    rw [he a, he b] at hc
    have hu : r (Additive.ofMul k) (e a) (e b) =
        r a (Additive.ofMul k) (e b) * (r a b (Additive.ofMul k))⁻¹ *
          conjugationTensorator ω k.val (e a).toMul (e b).toMul := by
      apply (inv_mul_eq_one).mp
      simpa only [r, mul_assoc] using hc
    have hcoef : (r (Additive.ofMul k) (e a) (e b) : ℂ) =
        (r a (Additive.ofMul k) (e b) : ℂ) *
          ((r a b (Additive.ofMul k) : ℂ)⁻¹ *
            (conjugationTensorator ω k.val (e a).toMul (e b).toMul : ℂ)) := by
      simpa only [Units.val_mul, Units.val_inv_eq_inv_val, mul_assoc] using
        congrArg (fun z : ℂˣ => (z : ℂ)) hu
    rw [BraidedCategory.braiding_tensor_right_hom]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [hcoef]
    simp only [Units.val_inv_eq_inv_val]
    rfl
  · exact ((tensorRight (Y b)).map_isZero
      ((tensorRight (X a)).map_isZero (simpleFiber_isZero _ _ _ hi))).eq_of_src _ _

end Paper18.Category.CrossedExtension
