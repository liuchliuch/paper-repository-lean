import Paper18.Category.CrossedExtensionInnerNormalizationCrossingTensor

/-! # The actual unit equation of canonical inner crossing -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open Functor.LaxMonoidal GradedObject.Monoidal
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec DrinfeldInner
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCrossingUnitKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The actual unit tensorator is the canonical degree-zero transport. -/
@[simp] lemma canonicalKernelPush_unit (g : KillingExtension G) :
    ε (canonicalKernelPush ω g) = (regradeUnitIso ((conjugationAut g⁻¹).toAdditive)).hom := rfl

end Paper18.Category.CrossedExtension
