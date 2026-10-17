import Paper18.Category.CrossedExtensionInnerNormalizationCrossingTensor
import Paper18.Category.CrossedExtensionInnerNormalizationComposition
import Paper18.Category.DrinfeldInnerTrivializationProduct

/-! # Actual product lines and normalization for kernel conjugation -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec DrinfeldInner
/-- The ordinary braided-category diagram underlying the product of
canonical crossings, including arbitrary actual line and fiber maps. -/
lemma innerProduct_fiber {A B R V W : FGModuleCat ℂ}
    (m : A ⊗ B ⟶ R) (v : V ⟶ W) :
    (α_ A B V).hom ≫ A ◁ (β_ B V).hom ≫ (α_ A V B).inv ≫
        (β_ A V).hom ▷ B ≫ (α_ V A B).hom ≫ v ▷ (A ⊗ B) ≫ W ◁ m =
      m ▷ V ≫ R ◁ v ≫ (β_ R W).hom := by
  rw [← BraidedCategory.braiding_tensor_left_hom_assoc]
  simpa only [MonoidalCategory.tensorHom_def, Category.assoc] using
    (BraidedCategory.braiding_naturality m v).symm

variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerProductKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- An actual product-line isomorphism. The comparison theorem is natural
in this isomorphism, so no arbitrary scalar normalization is assumed. -/
def kernelLineProductIso (k l : KillingKernel G) :
    kernelLine ω k ⊗ kernelLine ω l ≅ kernelLine ω (k * l) := by
  exact homogeneousTensorIso (Additive.ofMul k) (Additive.ofMul l)

/-- The actual fiber map of the chosen actual product-line isomorphism. -/
def kernelLineProductGenerator (k l : KillingKernel G) :
    (kernelLine ω k) (Additive.ofMul k) ⊗ (kernelLine ω l) (Additive.ofMul l) ⟶
      (kernelLine ω (k * l)) (Additive.ofMul (k * l)) :=
  GradedObject.Monoidal.ιTensorObj (kernelLine ω k) (kernelLine ω l)
      (Additive.ofMul k) (Additive.ofMul l) (Additive.ofMul (k * l)) rfl ≫
    (kernelLineProductIso ω k l).hom (Additive.ofMul (k * l))

/-- The coefficient of the actual product crossing is the actual θ
comparison; it cancels against the actual push multiplication scalar. -/
lemma canonicalInnerProduct_scalar (k l b : KillingKernel G) :
    (kernelCocycle ω).val k l b *
        ((kernelCocycle ω).val k (conjugate l.val b) l)⁻¹ *
        (kernelCocycle ω).val (conjugate (k.val * l.val) b) k l *
        (conjugationComparison ω k.val l.val b)⁻¹ = 1 := by
  apply Additive.ofMul.injective
  simp only [conjugationComparison, kernelCocycle, ofMul_mul, ofMul_inv, ofMul_one]
  abel

/-- Output-degree bookkeeping for the two successive actual crossings. -/
lemma canonicalInnerProduct_degree (k l : KillingKernel G)
    (a : Additive (KillingKernel G)) :
    Additive.ofMul k + Additive.ofMul l +
        Additive.ofMul (conjugate l.val⁻¹ (conjugate k.val⁻¹ a.toMul)) =
      a + Additive.ofMul k + Additive.ofMul l := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [conjugate, mul_assoc]

/-- The product coefficient cancellation in supported output coordinates. -/
lemma canonicalInnerProduct_scalar_output (k l b : KillingKernel G) :
    (kernelCocycle ω).val k l (conjugate l.val⁻¹ (conjugate k.val⁻¹ b)) *
        ((kernelCocycle ω).val k (conjugate k.val⁻¹ b) l)⁻¹ *
        (kernelCocycle ω).val b k l *
        (conjugationComparison ω k.val l.val
          (conjugate l.val⁻¹ (conjugate k.val⁻¹ b)))⁻¹ = 1 := by
  have hm : (k.val * l.val) * (l.val⁻¹ * k.val⁻¹) = 1 := by group
  have hm₂ : l.val * (l.val⁻¹ * k.val⁻¹) = k.val⁻¹ := by group
  simpa only [conjugate_conjugate, mul_inv_cancel, conjugate_unit, hm, hm₂] using
    canonicalInnerProduct_scalar ω k l (conjugate l.val⁻¹ (conjugate k.val⁻¹ b))

/-- An output-coordinate crossing formula with an explicit actual source
fiber transport, valid for any equal input-degree presentation. -/
@[reassoc]
lemma inclusion_canonicalInnerCrossing_output_ofEq (k : KillingKernel G)
    (X : CocycleVec (kernelCocycle ω)) (a b : Additive (KillingKernel G))
    (ha : a = Additive.ofMul (conjugate k.val⁻¹ b.toMul))
    (h : Additive.ofMul k + a = b + Additive.ofMul k) :
    GradedObject.Monoidal.ιTensorObj (kernelLine ω k) X
        (Additive.ofMul k) a (b + Additive.ofMul k) h ≫
        (canonicalInnerCrossing ω k X).hom (b + Additive.ofMul k) =
      (kernelLine ω k) (Additive.ofMul k) ◁ eqToHom (congrArg X ha) ≫
        (β_ ((kernelLine ω k) (Additive.ofMul k))
          (((canonicalKernelPush ω k.val).obj X) b)).hom ≫
        GradedObject.Monoidal.ιTensorObj ((canonicalKernelPush ω k.val).obj X)
          (kernelLine ω k) b (Additive.ofMul k) (b + Additive.ofMul k) rfl := by
  subst a
  simpa only [eqToHom_refl, whiskerLeft_id, id_comp] using
    inclusion_canonicalInnerCrossing_output ω k X b

end Paper18.Category.CrossedExtension
