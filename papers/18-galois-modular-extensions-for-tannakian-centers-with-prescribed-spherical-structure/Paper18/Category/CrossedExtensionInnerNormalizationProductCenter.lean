import Paper18.Category.CrossedExtensionInnerNormalizationProductDiagram
import Paper18.Category.CrossedExtensionInnerCenter
import Paper18.Category.DrinfeldInnerTrivializationComparison

/-! # Actual product coherence of the canonical inner center trivializations -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerProductCenterFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- An actual two-sided tensor inverse for the actual product line. -/
def kernelLineProductTensorInverse (k l : KillingKernel G) :
    TensorInverse (kernelLine ω k ⊗ kernelLine ω l) :=
  Classical.choice (IsTensorInvertible.tensor ⟨kernelLineTensorInverse ω k⟩
    ⟨kernelLineTensorInverse ω l⟩)

/-- The actual line-product comparison in the orientation needed for
cancelling the invertible product line. -/
theorem canonicalInnerCrossing_product (k l : KillingKernel G)
    (X : CocycleVec (kernelCocycle ω)) :
    (kernelLineProductIso ω k l).inv ▷ X ≫
        (productIntertwiner (canonicalKernelPush ω k.val) (canonicalKernelPush ω l.val)
          (kernelLine ω k) (kernelLine ω l)
          (canonicalInnerCrossingNatIso ω k) (canonicalInnerCrossingNatIso ω l) X).hom ≫
        (canonicalKernelPushMul ω k.val l.val).hom.app X ▷
          (kernelLine ω k ⊗ kernelLine ω l) ≫
        ((canonicalKernelPush ω (k.val * l.val)).obj X) ◁
          (kernelLineProductIso ω k l).hom =
      (canonicalInnerCrossing ω (k * l) X).hom := by
  have h := congrArg (fun z => (kernelLineProductIso ω k l).inv ▷ X ≫ z)
    (canonicalInnerCrossing_product_forward ω k l X (kernelLineProductIso ω k l).hom)
  simpa only [Category.assoc, ← comp_whiskerRight_assoc, Iso.inv_hom_id,
    id_whiskerRight, id_comp] using h

/-- Genuine half-braidings and the proved actual line multiplication
comparison give multiplication of the actual canonical trivializations. -/
theorem canonicalInnerTrivialization_mul (k l : KillingKernel G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (canonicalKernelPushMul ω k.val l.val).hom.app Z.1 ≫
        ((canonicalInnerTrivialization ω (k * l)).hom.app Z).f =
      ((canonicalInnerTrivialization ω k).hom.app
        ((DrinfeldEquivalence.map (canonicalKernelPush ω l.val)).obj Z)).f ≫
        ((canonicalInnerTrivialization ω l).hom.app Z).f := by
  exact productTrivialization_comparison
    (canonicalKernelPush ω k.val) (canonicalKernelPush ω l.val)
    (canonicalKernelPush ω (k.val * l.val))
    (kernelLine ω k) (kernelLine ω l) (kernelLine ω (k * l))
    (canonicalInnerCrossingNatIso ω k) (canonicalInnerCrossingNatIso ω l)
    (canonicalInnerCrossingNatIso ω (k * l))
    (canonicalInnerTrivialization ω k) (canonicalInnerTrivialization ω l)
    (canonicalInnerTrivialization ω (k * l)) (kernelLineProductTensorInverse ω k l)
    Z ((canonicalKernelPushMul ω k.val l.val).hom.app Z.1) (kernelLineProductIso ω k l)
    (canonicalInnerCrossing_product ω k l Z.1)
    (canonicalInnerTrivialization_intertwines ω k)
    (canonicalInnerTrivialization_intertwines ω l)
    (canonicalInnerTrivialization_intertwines ω (k * l) Z)

/-- Naturality rewrites the canonical product law in the action-compatible
order with the second trivialization mapped by the first translating functor. -/
theorem canonicalInnerTrivialization_mul_map (k l : KillingKernel G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (canonicalKernelPushMul ω k.val l.val).hom.app Z.1 ≫
        ((canonicalInnerTrivialization ω (k * l)).hom.app Z).f =
      (canonicalKernelPush ω k.val).map
          (((canonicalInnerTrivialization ω l).hom.app Z).f) ≫
        ((canonicalInnerTrivialization ω k).hom.app Z).f := by
  rw [canonicalInnerTrivialization_mul]
  have hn := congrArg Center.Hom.f
    ((canonicalInnerTrivialization ω k).hom.naturality
      ((canonicalInnerTrivialization ω l).hom.app Z))
  exact hn.symm

end Paper18.Category.CrossedExtension
