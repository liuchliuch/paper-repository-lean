import Paper18.Category.DrinfeldInnerTrivializationTensor
import Paper18.Category.DrinfeldEquivalenceMapAction
import Paper18.Category.CrossedExtensionInnerNormalizationCrossing
import Paper18.Category.QuasiFusionPivotal

/-! # Actual kernel-line cancellation on the underlying center functor -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCenterBasicFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The actual inverse of the actual kernel homogeneous line. -/
def kernelLineTensorInverse (k : KillingKernel G) : TensorInverse (kernelLine ω k) :=
  CocycleVec.homogeneousTensorInverse (kernelCocycle ω) (Additive.ofMul k)

/-- Actual cancellation of the invertible homogeneous line constructs
this natural isomorphism from the genuine center half-braiding. -/
def canonicalInnerUnderlyingTrivialization (k : KillingKernel G) :
    DrinfeldEquivalence.map (canonicalKernelPush ω k.val) ⋙
      Center.forget (CocycleVec (kernelCocycle ω)) ≅
        Center.forget (CocycleVec (kernelCocycle ω)) :=
  underlyingOfIntertwiner (canonicalKernelPush ω k.val) (kernelLine ω k)
    (canonicalInnerCrossingNatIso ω k) (kernelLineTensorInverse ω k)

/-- The constructed comparison satisfies its actual half-braiding equation. -/
lemma canonicalInnerUnderlyingTrivialization_intertwines (k : KillingKernel G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (canonicalInnerCrossing ω k Z.1).hom ≫
        (canonicalInnerUnderlyingTrivialization ω k).hom.app Z ▷ kernelLine ω k =
      (Z.2.β (kernelLine ω k)).inv :=
  underlyingOfIntertwiner_intertwines (canonicalKernelPush ω k.val) (kernelLine ω k)
    (canonicalInnerCrossingNatIso ω k) (kernelLineTensorInverse ω k) Z

/-- The actual normalization exhibits the original translation as an equivalence. -/
instance kernelInnerTranslation_isEquivalence (g : KillingExtension G) :
    (kernelTranslation ω g).IsEquivalence :=
  Functor.isEquivalence_of_iso (kernelPushNormalization ω g).symm

/-- The actual normalization converts the canonical comparison to the
original constructed kernel action convention. -/
def kernelInnerUnderlyingTrivialization (k : KillingKernel G) :
    DrinfeldEquivalence.map (kernelTranslation ω k.val) ⋙
      Center.forget (CocycleVec (kernelCocycle ω)) ≅
        Center.forget (CocycleVec (kernelCocycle ω)) :=
  Functor.isoWhiskerRight (DrinfeldEquivalence.mapNatIso (kernelPushNormalization ω k.val))
    (Center.forget _) ≪≫ canonicalInnerUnderlyingTrivialization ω k

end Paper18.Category.CrossedExtension
