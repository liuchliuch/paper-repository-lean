import Paper18.Category.CrossedExtensionInnerNormalizationCrossing

/-! # Tensor coherence of canonical crossing with a kernel line -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec DrinfeldInner

private lemma unitFiber_crossing {L V W : FGModuleCat ℂ}
    (u : L ≅ 𝟙_ (FGModuleCat ℂ)) (f : V ⟶ W) :
    (u.hom ▷ V) ≫ (λ_ V).hom ≫ f ≫ (ρ_ W).inv ≫ W ◁ u.inv =
      (β_ L V).hom ≫ f ▷ L := by
  apply (cancel_mono (W ◁ u.hom)).mp
  simp only [Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
    whiskerLeft_id, comp_id]
  rw [← whisker_exchange, ← BraidedCategory.braiding_naturality_left_assoc]
  simp only [braiding_tensorUnit_left, Category.assoc]
  rw [rightUnitor_inv_naturality]

variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCrossingTensorKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The scalar in the actual crossing tensor diagram is exactly one,
by the explicitly constructed conjugation tensorator. -/
lemma canonicalInnerCrossing_scalar (k a b : KillingKernel G) :
    ((kernelCocycle ω).val k a b)⁻¹ *
        (kernelCocycle ω).val (conjugate k.val a) k b *
        ((kernelCocycle ω).val (conjugate k.val a) (conjugate k.val b) k)⁻¹ *
        conjugationTensorator ω k.val a b = 1 := by
  apply Additive.ofMul.injective
  simp only [conjugationTensorator, kernelCocycle, ofMul_mul, ofMul_inv, ofMul_one]
  abel

/-- The actual source fiber in a supported line summand agrees with the
corresponding fiber of the conjugated object. -/
lemma canonicalInner_degree_input (k : KillingKernel G)
    (a s : Additive (KillingKernel G)) (h : Additive.ofMul k + a = s) :
    a = Additive.ofMul (conjugate k.val⁻¹ (s - Additive.ofMul k).toMul) := by
  calc
    a = -Additive.ofMul k + s := by rw [← h]; simp
    _ = _ := canonicalInner_degree k s

@[reassoc]
lemma inclusion_canonicalInnerCrossing (k : KillingKernel G)
    (X : CocycleVec (kernelCocycle ω)) (a s : Additive (KillingKernel G))
    (h : Additive.ofMul k + a = s) :
    GradedObject.Monoidal.ιTensorObj
        (simpleObject (Additive (KillingKernel G)) (Additive.ofMul k)) X
        (Additive.ofMul k) a s h ≫ (canonicalInnerCrossing ω k X).hom s =
      (β_ ((simpleObject (Additive (KillingKernel G)) (Additive.ofMul k))
        (Additive.ofMul k)) (X a)).hom ≫
        eqToHom (congrArg X (canonicalInner_degree_input k a s h)) ▷
          ((simpleObject (Additive (KillingKernel G)) (Additive.ofMul k)) (Additive.ofMul k)) ≫
        GradedObject.Monoidal.ιTensorObj ((canonicalKernelPush ω k.val).obj X)
          (simpleObject (Additive (KillingKernel G)) (Additive.ofMul k))
          (s - Additive.ofMul k) (Additive.ofMul k) s (sub_add_cancel s _) := by
  rw [canonicalInnerCrossing_hom_apply]
  change tensorInclusion _ _ _ _ _ _ _ ≫
      leftLineProjection X (Additive.ofMul k) s ≫ _ = _
  rw [inclusion_leftLineProjection_assoc]
  simp only [rightLineInclusion, eqToHom_trans_assoc]
  exact congrArg (fun q => q ≫ GradedObject.Monoidal.ιTensorObj
    ((canonicalKernelPush ω k.val).obj X)
    (simpleObject (Additive (KillingKernel G)) (Additive.ofMul k))
    (s - Additive.ofMul k) (Additive.ofMul k) s (sub_add_cancel s _))
    (unitFiber_crossing (simpleFiberIso _ _) (eqToHom
      (congrArg X (canonicalInner_degree_input k a s h))))

/-- The supported degree equality in output coordinates. -/
lemma canonicalInner_output_degree (k : KillingKernel G) (a : Additive (KillingKernel G)) :
    Additive.ofMul k + Additive.ofMul (conjugate k.val⁻¹ a.toMul) = a + Additive.ofMul k := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [conjugate, mul_assoc]

@[reassoc]
lemma inclusion_canonicalInnerCrossing_output (k : KillingKernel G)
    (X : CocycleVec (kernelCocycle ω)) (a : Additive (KillingKernel G)) :
    GradedObject.Monoidal.ιTensorObj
        (simpleObject (Additive (KillingKernel G)) (Additive.ofMul k)) X
        (Additive.ofMul k) (Additive.ofMul (conjugate k.val⁻¹ a.toMul))
        (a + Additive.ofMul k) (canonicalInner_output_degree k a) ≫
        (canonicalInnerCrossing ω k X).hom (a + Additive.ofMul k) =
      (β_ ((simpleObject (Additive (KillingKernel G)) (Additive.ofMul k))
        (Additive.ofMul k)) (((canonicalKernelPush ω k.val).obj X) a)).hom ≫
        GradedObject.Monoidal.ιTensorObj ((canonicalKernelPush ω k.val).obj X)
          (simpleObject (Additive (KillingKernel G)) (Additive.ofMul k))
          a (Additive.ofMul k) (a + Additive.ofMul k) rfl := by
  have hh := inclusion_canonicalInnerCrossing ω k X
    (Additive.ofMul (conjugate k.val⁻¹ a.toMul)) (a + Additive.ofMul k)
    (canonicalInner_output_degree k a)
  rw [hh]
  congr 1
  have hq : a + Additive.ofMul k - Additive.ofMul k = a := add_sub_cancel_right _ _
  have htransport : eqToHom (congrArg X (canonicalInner_degree_input k
      (Additive.ofMul (conjugate k.val⁻¹ a.toMul)) (a + Additive.ofMul k)
      (canonicalInner_output_degree k a))) ▷
        ((simpleObject (Additive (KillingKernel G)) (Additive.ofMul k)) (Additive.ofMul k)) =
      eqToHom (congrArg (fun j => ((canonicalKernelPush ω k.val).obj X) j ⊗
        ((simpleObject (Additive (KillingKernel G)) (Additive.ofMul k)) (Additive.ofMul k))) hq.symm) := by
    exact eqToHom_whiskerRight _ _
  rw [htransport]
  exact eqToHom_tensorInclusion _ _ hq rfl _ _ _


end Paper18.Category.CrossedExtension
