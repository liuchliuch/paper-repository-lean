import Paper18.Category.CrossedExtensionInnerNormalization
import Paper18.Category.DrinfeldInnerTrivializationLines

/-! # The actual canonical crossing with a kernel homogeneous line -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCrossingKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The actual kernel homogeneous line in the twisted category. -/
def kernelLine (k : KillingKernel G) : CocycleVec (kernelCocycle ω) :=
  simpleObject (Additive (KillingKernel G)) (Additive.ofMul k)

/-- The actual equality of supported fibers for inner conjugation. -/
lemma canonicalInner_degree (k : KillingKernel G) (s : Additive (KillingKernel G)) :
    -Additive.ofMul k + s =
      Additive.ofMul (conjugate k.val⁻¹ (s - Additive.ofMul k).toMul) := by
  apply Additive.toMul.injective
  apply Subtype.ext
  simp [conjugate, sub_eq_add_neg, mul_assoc]

/-- Crossing the degree-`k` line to the right has coefficient one in the
actual supported convolution fibers. -/
def canonicalInnerCrossing (k : KillingKernel G) (X : CocycleVec (kernelCocycle ω)) :
    kernelLine ω k ⊗ X ≅
      (canonicalKernelPush ω k.val).obj X ⊗
        kernelLine ω k :=
  GradedObject.isoMk _ _ (fun s =>
    leftLineFiberIso X (Additive.ofMul k) s ≪≫
      eqToIso (congrArg X (canonicalInner_degree k s)) ≪≫
        (rightLineFiberIso ((canonicalKernelPush ω k.val).obj X) (Additive.ofMul k) s).symm)

@[simp] lemma canonicalInnerCrossing_hom_apply (k : KillingKernel G)
    (X : CocycleVec (kernelCocycle ω)) (s : Additive (KillingKernel G)) :
    (canonicalInnerCrossing ω k X).hom s =
      leftLineProjection X (Additive.ofMul k) s ≫
        eqToHom (congrArg X (canonicalInner_degree k s)) ≫
          rightLineInclusion ((canonicalKernelPush ω k.val).obj X) (Additive.ofMul k) s := rfl

/-- Naturality holds for every actual graded linear map. -/
@[reassoc]
theorem canonicalInnerCrossing_naturality (k : KillingKernel G)
    {X Y : CocycleVec (kernelCocycle ω)} (f : X ⟶ Y) :
    kernelLine ω k ◁ f ≫
        (canonicalInnerCrossing ω k Y).hom =
      (canonicalInnerCrossing ω k X).hom ≫
        (canonicalKernelPush ω k.val).map f ▷
          kernelLine ω k := by
  apply GradedObject.hom_ext
  intro s
  change GradedObject.Monoidal.tensorHom
      (𝟙 (simpleObject (Additive (KillingKernel G)) (Additive.ofMul k))) f s ≫
      (canonicalInnerCrossing ω k Y).hom s =
    (canonicalInnerCrossing ω k X).hom s ≫ GradedObject.Monoidal.tensorHom
      ((canonicalKernelPush ω k.val).map f)
      (𝟙 (simpleObject (Additive (KillingKernel G)) (Additive.ofMul k))) s
  rw [canonicalInnerCrossing_hom_apply, canonicalInnerCrossing_hom_apply,
    leftLineProjection_naturality_assoc]
  have he := eqToHom_naturality f (canonicalInner_degree k s)
  rw [reassoc_of% he]
  have hr := rightLineInclusion_naturality ((canonicalKernelPush ω k.val).map f)
    (Additive.ofMul k) s
  exact congrArg (fun q => leftLineProjection X (Additive.ofMul k) s ≫
    eqToHom (congrArg X (canonicalInner_degree k s)) ≫ q) hr

/-- An actual natural isomorphism between the two tensor-by-line functors. -/
def canonicalInnerCrossingNatIso (k : KillingKernel G) :
    tensorLeft (kernelLine ω k) ≅
      canonicalKernelPush ω k.val ⋙
        tensorRight (kernelLine ω k) :=
  NatIso.ofComponents (canonicalInnerCrossing ω k)
    (fun f => canonicalInnerCrossing_naturality ω k f)

end Paper18.Category.CrossedExtension
