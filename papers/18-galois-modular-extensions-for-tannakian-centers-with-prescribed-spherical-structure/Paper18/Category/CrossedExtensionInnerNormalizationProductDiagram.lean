import Paper18.Category.CrossedExtensionInnerNormalizationProductBasic

/-! # Actual product comparison of the canonical kernel-line crossings -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal GradedObject.Monoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerProductDiagramFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The product of two genuine canonical crossings agrees with the crossing
of the product line, after the actual push multiplication comparison. -/
theorem canonicalInnerCrossing_product_forward (k l : KillingKernel G)
    (X : CocycleVec (kernelCocycle ω))
    (q : kernelLine ω k ⊗ kernelLine ω l ⟶ kernelLine ω (k * l)) :
    (productIntertwiner (canonicalKernelPush ω k.val) (canonicalKernelPush ω l.val)
        (kernelLine ω k) (kernelLine ω l)
        (canonicalInnerCrossingNatIso ω k) (canonicalInnerCrossingNatIso ω l) X).hom ≫
        (canonicalKernelPushMul ω k.val l.val).hom.app X ▷
          (kernelLine ω k ⊗ kernelLine ω l) ≫
        ((canonicalKernelPush ω (k.val * l.val)).obj X) ◁ q =
      q ▷ X ≫ (canonicalInnerCrossing ω (k * l) X).hom := by
  let L := kernelLine ω k
  let M := kernelLine ω l
  let R := kernelLine ω (k * l)
  let F := canonicalKernelPush ω k.val
  let H := canonicalKernelPush ω l.val
  let Q := canonicalKernelPush ω (k.val * l.val)
  let e := (conjugationAut k.val⁻¹).toAdditive
  let f := (conjugationAut l.val⁻¹).toAdditive
  let d := (conjugationAut (k.val * l.val)⁻¹).toAdditive
  let r := fun a b c : Additive (KillingKernel G) => (kernelCocycle ω).val a.toMul b.toMul c.toMul
  have hTensor (U V : CocycleVec (kernelCocycle ω)) :
      U ⊗ V = GradedObject.Monoidal.tensorObj U V := rfl
  have he (b : Additive (KillingKernel G)) : f (e b) = d b := by
    change Additive.ofMul (conjugate l.val⁻¹ (conjugate k.val⁻¹ b.toMul)) =
      Additive.ofMul (conjugate (k.val * l.val)⁻¹ b.toMul)
    simp only [conjugate_conjugate, mul_inv_rev]
  have hk (b : Additive (KillingKernel G)) : Additive.ofMul k + e b = b + Additive.ofMul k :=
    canonicalInner_output_degree k b
  have hl (b : Additive (KillingKernel G)) : Additive.ofMul l + f b = b + Additive.ofMul l :=
    canonicalInner_output_degree l b
  have hγl (b : Additive (KillingKernel G)) :
      ιTensorObj M X (Additive.ofMul l) (f b) (b + Additive.ofMul l) (hl b) ≫
          (canonicalInnerCrossing ω l X).hom (b + Additive.ofMul l) =
        (β_ (M (Additive.ofMul l)) (H.obj X b)).hom ≫
          ιTensorObj (H.obj X) M b (Additive.ofMul l) (b + Additive.ofMul l) rfl :=
    inclusion_canonicalInnerCrossing_output ω l X b
  have hγk (b : Additive (KillingKernel G)) :
      ιTensorObj L (H.obj X) (Additive.ofMul k) (e b) (b + Additive.ofMul k) (hk b) ≫
          (canonicalInnerCrossing ω k (H.obj X)).hom (b + Additive.ofMul k) =
        (β_ (L (Additive.ofMul k)) (F.obj (H.obj X) b)).hom ≫
          ιTensorObj (F.obj (H.obj X)) L b (Additive.ofMul k) (b + Additive.ofMul k) rfl :=
    inclusion_canonicalInnerCrossing_output ω k (H.obj X) b
  apply GradedObject.hom_ext
  intro s
  apply tensorObj₃'_ext (X₁ := L) (X₂ := M) (X₃ := X)
  intro i j a h
  by_cases hi : i = Additive.ofMul k
  · subst i
    by_cases hj : j = Additive.ofMul l
    · subst j
      obtain ⟨b, rfl⟩ := (e.trans f).surjective a
      have hd : Additive.ofMul k + Additive.ofMul l + f (e b) =
          b + Additive.ofMul (k * l) := by
        simpa only [ofMul_mul, add_assoc] using canonicalInnerProduct_degree k l b
      have hs : s = b + Additive.ofMul (k * l) := h.symm.trans hd
      subst hs
      have hab : Additive.ofMul k + Additive.ofMul l = Additive.ofMul (k * l) := rfl
      have hγR := inclusion_canonicalInnerCrossing_output_ofEq ω (k * l) X
        (f (e b)) b (he b) (by simpa only [ofMul_mul, add_assoc] using hd)
      change ιTensorObj₃' L M X (Additive.ofMul k) (Additive.ofMul l) (f (e b))
          (b + Additive.ofMul (k * l)) h ≫
          ((scalarAssociator r L M X).hom (b + Additive.ofMul (k * l)) ≫
            GradedObject.Monoidal.whiskerLeft L (canonicalInnerCrossing ω l X).hom
              (b + Additive.ofMul (k * l)) ≫
            (scalarAssociator r L (H.obj X) M).inv (b + Additive.ofMul (k * l)) ≫
            GradedObject.Monoidal.whiskerRight
              (canonicalInnerCrossing ω k (H.obj X)).hom M (b + Additive.ofMul (k * l)) ≫
            (scalarAssociator r (F.obj (H.obj X)) L M).hom (b + Additive.ofMul (k * l)) ≫
            GradedObject.Monoidal.whiskerRight
              ((canonicalKernelPushMul ω k.val l.val).hom.app X) (GradedObject.Monoidal.tensorObj L M)
                (b + Additive.ofMul (k * l)) ≫
            GradedObject.Monoidal.whiskerLeft (Q.obj X) q (b + Additive.ofMul (k * l))) =
        ιTensorObj₃' L M X (Additive.ofMul k) (Additive.ofMul l) (f (e b))
          (b + Additive.ofMul (k * l)) h ≫
          (GradedObject.Monoidal.whiskerRight q X (b + Additive.ofMul (k * l)) ≫
            (canonicalInnerCrossing ω (k * l) X).hom (b + Additive.ofMul (k * l)))
      dsimp only [CocycleVec.instMonoidalCategory, twistedMonoidalCategory, scalarMonoidalCategory,
        PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
      conv_rhs =>
        rw [ιTensorObj₃'_eq L M X (Additive.ofMul k) (Additive.ofMul l) (f (e b))
          (b + Additive.ofMul (k * l)) h (Additive.ofMul (k * l)) hab,
          Category.assoc, ι_tensorHom_assoc]
        dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
        rw [MonoidalCategory.tensorHom_id, ← MonoidalCategory.comp_whiskerRight_assoc]
        simp only [Category.assoc]
        rw [hγR]
      conv_lhs =>
        rw [inclusion_scalarAssociator_assoc]
        simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
        rw [ιTensorObj₃_eq L M X (Additive.ofMul k) (Additive.ofMul l) (f (e b))
          (b + Additive.ofMul (k * l)) h (e b + Additive.ofMul l) (hl (e b)),
          Category.assoc, ι_tensorHom_assoc]
        dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
        rw [MonoidalCategory.id_tensorHom, ← MonoidalCategory.whiskerLeft_comp_assoc]
        simp only [Category.assoc]
        rw [hγl (e b)]
        dsimp only [CocycleVec.instMonoidalCategory, twistedMonoidalCategory, scalarMonoidalCategory,
          PointedVec.instMonoidalCategory, GradedObject.monoidalCategory]
        simp only [whiskerLeft_comp, Category.assoc, hTensor]
        change (r (Additive.ofMul k) (Additive.ofMul l) (f (e b)) : ℂ) •
          ((α_ (L (Additive.ofMul k)) (M (Additive.ofMul l)) (X (f (e b)))).hom ≫
            L (Additive.ofMul k) ◁ (β_ (M (Additive.ofMul l)) (H.obj X (e b))).hom ≫
            L (Additive.ofMul k) ◁ ιTensorObj (H.obj X) M (e b) (Additive.ofMul l)
              (e b + Additive.ofMul l) rfl ≫
            ιTensorObj L (GradedObject.Monoidal.tensorObj (H.obj X) M) (Additive.ofMul k)
              (e b + Additive.ofMul l) (b + Additive.ofMul (k * l))
              (by rw [← add_assoc, hk b, add_assoc]; rfl) ≫
            (scalarAssociator r L (H.obj X) M).inv (b + Additive.ofMul (k * l)) ≫
            GradedObject.Monoidal.whiskerRight (canonicalInnerCrossing ω k (H.obj X)).hom M
              (b + Additive.ofMul (k * l)) ≫
            (scalarAssociator r (F.obj (H.obj X)) L M).hom (b + Additive.ofMul (k * l)) ≫
            GradedObject.Monoidal.whiskerRight ((canonicalKernelPushMul ω k.val l.val).hom.app X)
              (GradedObject.Monoidal.tensorObj L M) (b + Additive.ofMul (k * l)) ≫
            GradedObject.Monoidal.whiskerLeft (Q.obj X) q (b + Additive.ofMul (k * l)))
        rw [← ιTensorObj₃_eq_assoc L (H.obj X) M (Additive.ofMul k) (e b) (Additive.ofMul l)
          (b + Additive.ofMul (k * l)) (by rw [hk b, add_assoc]; rfl)
          (e b + Additive.ofMul l) rfl, inclusion_scalarAssociator_inv_assoc]
        simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
        rw [ιTensorObj₃'_eq L (H.obj X) M (Additive.ofMul k) (e b) (Additive.ofMul l)
          (b + Additive.ofMul (k * l)) (by rw [hk b, add_assoc]; rfl)
          (b + Additive.ofMul k) (hk b), Category.assoc, ι_tensorHom_assoc]
        dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
        rw [MonoidalCategory.tensorHom_id, ← MonoidalCategory.comp_whiskerRight_assoc]
        simp only [Category.assoc]
        tactic =>
          exact congrArg (fun z => (r (Additive.ofMul k) (Additive.ofMul l) (f (e b)) : ℂ) •
            (((r (Additive.ofMul k) (e b) (Additive.ofMul l))⁻¹ : ℂˣ).val •
              ((α_ (L (Additive.ofMul k)) (M (Additive.ofMul l)) (X (f (e b)))).hom ≫
                L (Additive.ofMul k) ◁ (β_ (M (Additive.ofMul l)) (H.obj X (e b))).hom ≫
                (α_ (L (Additive.ofMul k)) (H.obj X (e b)) (M (Additive.ofMul l))).inv ≫
                z ▷ M (Additive.ofMul l) ≫
                ιTensorObj (GradedObject.Monoidal.tensorObj (F.obj (H.obj X)) L) M
                  (b + Additive.ofMul k) (Additive.ofMul l) (b + Additive.ofMul (k * l))
                  (by rw [add_assoc]; rfl) ≫
                (scalarAssociator r (F.obj (H.obj X)) L M).hom (b + Additive.ofMul (k * l)) ≫
                GradedObject.Monoidal.whiskerRight ((canonicalKernelPushMul ω k.val l.val).hom.app X)
                  (GradedObject.Monoidal.tensorObj L M) (b + Additive.ofMul (k * l)) ≫
                GradedObject.Monoidal.whiskerLeft (Q.obj X) q (b + Additive.ofMul (k * l)))))
            (hγk b)
      dsimp only
      simp only [comp_whiskerRight, Category.assoc]
      conv_lhs =>
        rw [← ιTensorObj₃'_eq_assoc (F.obj (H.obj X)) L M b (Additive.ofMul k) (Additive.ofMul l)
          (b + Additive.ofMul (k * l)) (by rw [add_assoc]; rfl)
          (b + Additive.ofMul k) rfl, inclusion_scalarAssociator_assoc]
        simp only [Linear.smul_comp, Linear.comp_smul, Category.assoc]
        rw [ιTensorObj₃_eq (F.obj (H.obj X)) L M b (Additive.ofMul k) (Additive.ofMul l)
          (b + Additive.ofMul (k * l)) (by rw [add_assoc]; rfl)
          (Additive.ofMul (k * l)) hab, Category.assoc, ι_tensorHom_assoc]
        dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
        rw [MonoidalCategory.tensorHom_id, ι_tensorHom]
        dsimp only [PointedVec.id_apply, GradedObject.categoryOfGradedObjects_id]
        rw [MonoidalCategory.id_tensorHom]
        simp only [Category.assoc]
      have hξ : (canonicalKernelPushMul ω k.val l.val).hom.app X b =
          (((conjugationComparison ω k.val l.val (f (e b)).toMul)⁻¹ : ℂˣ) : ℂ) •
            eqToHom (congrArg X (he b)) := by
        rw [canonicalKernelPushMul_hom_app]
        congr 1
        exact congrArg (fun z : KillingKernel G =>
          (((conjugationComparison ω k.val l.val z)⁻¹ : ℂˣ) : ℂ))
          (congrArg Additive.toMul (he b)).symm
      conv_lhs =>
        rw [MonoidalCategory.whisker_exchange_assoc, hξ]
        simp only [MonoidalLinear.smul_whiskerRight, Linear.smul_comp, Linear.comp_smul,
          Category.assoc, smul_smul]
      have hc := congrArg (fun z : ℂˣ => (z : ℂ))
        (canonicalInnerProduct_scalar_output ω k l b.toMul)
      have hcoef : (r (Additive.ofMul k) (Additive.ofMul l) (f (e b)) : ℂ) *
          (((r (Additive.ofMul k) (e b) (Additive.ofMul l))⁻¹ : ℂˣ).val *
            ((r b (Additive.ofMul k) (Additive.ofMul l) : ℂ) *
              (((conjugationComparison ω k.val l.val (f (e b)).toMul)⁻¹ : ℂˣ) : ℂ))) = 1 := by
        simpa only [r, e, f, MulEquiv.toAdditive, conjugationAut, toMul_ofMul,
          Units.val_mul, Units.val_inv_eq_inv_val, Units.val_one, mul_assoc] using hc
      rw [hcoef, one_smul]
      rw [← MonoidalCategory.whiskerLeft_comp_assoc, ← MonoidalCategory.comp_whiskerRight_assoc]
      simpa only [Category.assoc] using congrArg
        (fun z => z ≫ ιTensorObj (Q.obj X) R b (Additive.ofMul (k * l))
        (b + Additive.ofMul (k * l)) rfl)
        (innerProduct_fiber
          (ιTensorObj L M (Additive.ofMul k) (Additive.ofMul l) (Additive.ofMul (k * l)) hab ≫
            q (Additive.ofMul (k * l)))
          (eqToHom (congrArg X (he b))))
    · exact ((tensorRight (X a)).map_isZero
        ((tensorLeft (L (Additive.ofMul k))).map_isZero (simpleFiber_isZero _ _ _ hj))).eq_of_src _ _
  · exact ((tensorRight (X a)).map_isZero
      ((tensorRight (M j)).map_isZero (simpleFiber_isZero _ _ _ hi))).eq_of_src _ _

end Paper18.Category.CrossedExtension
