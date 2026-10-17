import Paper18.Category.CrossedExtensionInnerCenter
import Paper18.Category.CrossedExtensionInnerCenterConjugationDiagram
import Paper18.Category.CrossedExtensionInnerCenterConjugationCoherence

/-! # Actual conjugation compatibility of the constructed center trivializations -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCenterConjugationLiftFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The genuine line-conjugation diagram and the actual center half-braiding
derive equivariance of the constructed kernel trivializations. -/
theorem canonicalInnerTrivialization_conjugation (g : KillingExtension G)
    (k : KillingKernel G) (Z : Center (CocycleVec (kernelCocycle ω))) :
    (canonicalKernelPushConjugationIso ω g k).hom.app Z.1 ≫
        ((canonicalInnerTrivialization ω (conjugate g k)).hom.app
          ((DrinfeldEquivalence.map (canonicalKernelPush ω g)).obj Z)).f =
      (canonicalKernelPush ω g).map (((canonicalInnerTrivialization ω k).hom.app Z).f) := by
  apply imageTrivialization_comparison (canonicalKernelPush ω g) Z
    ((canonicalKernelPush ω k.val).obj Z.1) (kernelLine ω k)
    (kernelLine ω (conjugate g k))
    ((canonicalKernelPush ω (conjugate g k).val).obj ((canonicalKernelPush ω g).obj Z.1))
    (canonicalInnerCrossing ω k Z.1) (kernelLineTensorInverse ω k)
    (((canonicalInnerTrivialization ω k).hom.app Z).f)
    (canonicalInnerCrossing ω (conjugate g k) ((canonicalKernelPush ω g).obj Z.1)).hom
    ((canonicalKernelPushConjugationIso ω g k).hom.app Z.1)
    (kernelLineImageIso ω g k)
    (((canonicalInnerTrivialization ω (conjugate g k)).hom.app
      ((DrinfeldEquivalence.map (canonicalKernelPush ω g)).obj Z)).f)
  · simpa only [imageIntertwiner, Iso.trans_hom, Functor.mapIso_hom,
      Iso.symm_hom, Functor.Monoidal.μIso_hom, Functor.Monoidal.μIso_inv,
      Category.assoc] using canonicalInnerCrossing_conjugation ω g k Z.1
  · exact canonicalInnerTrivialization_intertwines ω k Z
  · exact canonicalInnerTrivialization_intertwines ω (conjugate g k)
      ((DrinfeldEquivalence.map (canonicalKernelPush ω g)).obj Z)

end Paper18.Category.CrossedExtension
