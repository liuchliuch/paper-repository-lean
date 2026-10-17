import Paper18.Category.CrossedExtensionInnerCenterBasic
import Paper18.Category.CrossedExtensionInnerNormalizationHexagon

/-! # Actual monoidal trivialization of kernel inner conjugation on the center -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCenterFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The proved actual crossing hexagon is the actual tensor-intertwiner equation. -/
lemma canonicalInnerCrossing_tensor (k : KillingKernel G)
    (X Y : CocycleVec (kernelCocycle ω)) :
    (canonicalInnerCrossingNatIso ω k).hom.app (X ⊗ Y) =
      (conjugatingTensorIso (canonicalKernelPush ω k.val) (kernelLine ω k)
        (canonicalInnerCrossingNatIso ω k) X Y).hom ≫
          μ (canonicalKernelPush ω k.val) X Y ▷ kernelLine ω k := by
  have h := congrArg (fun q => (α_ (kernelLine ω k) X Y).inv ≫ q)
    (canonicalInnerCrossing_tensor_forward ω k X Y)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc,
    conjugatingTensorIso, Iso.trans_hom, Iso.symm_hom,
    whiskerLeftIso_hom, whiskerRightIso_hom] using h

/-- The actual center lift of inner conjugation is actually monoidally
isomorphic to the identity. The natural comparison is constructed from
actual half-braidings and cancellation of the actual invertible line. -/
def canonicalInnerTrivialization (k : KillingKernel G) :
    DrinfeldEquivalence.map (canonicalKernelPush ω k.val) ≅
      𝟭 (Center (CocycleVec (kernelCocycle ω))) :=
  trivializationOfIntertwinerOfTensor (canonicalKernelPush ω k.val) (kernelLine ω k)
    (canonicalInnerCrossingNatIso ω k) (CocycleVec.skeleton (kernelCocycle ω))
    (CocycleVec.pivotalStructure (kernelCocycle ω)) (kernelLineTensorInverse ω k)
    (canonicalInnerCrossing_tensor ω k)

instance canonicalInnerTrivialization_monoidal (k : KillingKernel G) :
    NatTrans.IsMonoidal (canonicalInnerTrivialization ω k).hom := by
  delta canonicalInnerTrivialization
  infer_instance

lemma canonicalInnerTrivialization_intertwines (k : KillingKernel G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (canonicalInnerCrossing ω k Z.1).hom ≫
        ((canonicalInnerTrivialization ω k).hom.app Z).f ▷ kernelLine ω k =
      (Z.2.β (kernelLine ω k)).inv :=
  canonicalInnerUnderlyingTrivialization_intertwines ω k Z

/-- The actual primitive normalization supplies the corresponding actual
monoidal trivialization in the original kernel action convention. -/
def kernelInnerTrivialization (k : KillingKernel G) :
    DrinfeldEquivalence.map (kernelTranslation ω k.val) ≅
      𝟭 (Center (CocycleVec (kernelCocycle ω))) :=
  DrinfeldEquivalence.mapNatIso (kernelPushNormalization ω k.val) ≪≫
    canonicalInnerTrivialization ω k

instance kernelInnerTrivialization_monoidal (k : KillingKernel G) :
    NatTrans.IsMonoidal (kernelInnerTrivialization ω k).hom := by
  delta kernelInnerTrivialization
  infer_instance

@[simp] lemma kernelInnerTrivialization_hom_app_f (k : KillingKernel G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    ((kernelInnerTrivialization ω k).hom.app Z).f =
      (kernelPushNormalization ω k.val).hom.app Z.1 ≫
        ((canonicalInnerTrivialization ω k).hom.app Z).f := rfl

end Paper18.Category.CrossedExtension
