import Paper18.Category.CrossedExtensionInnerCenterConjugationTensor
import Paper18.Category.CrossedExtensionInnerNormalizationCrossingTensor

/-! # Actual line crossings with explicit degree transports -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open GradedObject.Monoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerConjugationCrossingFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The genuine crossing on a convolution summand, retaining the actual
transport between the two propositionally equal source fibers. -/
@[reassoc] lemma inclusion_canonicalInnerCrossing_transport
    (k : KillingKernel G) (X : CocycleVec (kernelCocycle ω))
    (i j a s : Additive (KillingKernel G))
    (hi : i = Additive.ofMul k)
    (hj : j = Additive.ofMul (conjugate k.val⁻¹ a.toMul))
    (h : i + j = s) (h' : a + i = s) :
    ιTensorObj (kernelLine ω k) X i j s h ≫ (canonicalInnerCrossing ω k X).hom s =
      (β_ ((kernelLine ω k) i) (X j)).hom ≫
        eqToHom (congrArg X hj) ▷ ((kernelLine ω k) i) ≫
          ιTensorObj ((canonicalKernelPush ω k.val).obj X) (kernelLine ω k) a i s h' := by
  subst i
  subst j
  rcases h' with rfl
  simpa only [eqToHom_refl, id_whiskerRight, id_comp] using
    inclusion_canonicalInnerCrossing_output ω k X a

end Paper18.Category.CrossedExtension
