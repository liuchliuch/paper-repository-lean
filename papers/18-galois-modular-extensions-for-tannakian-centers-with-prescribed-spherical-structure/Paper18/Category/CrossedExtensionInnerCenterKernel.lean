import Paper18.Category.CrossedExtensionInnerCenterConjugation
import Paper18.Category.CrossedExtensionInnerCenterAction
import Paper18.Category.WeakActionQuotientStandardTransport

/-! # Actual canonical kernel comparisons in quotient-action coordinates -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCenterKernelFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- The constructed actual kernel trivialization, typed over the actual
canonical weak action rather than its definitionally equal center lift. -/
def canonicalKernelCenterTrivialization (k : KillingKernel G) :
    (canonicalKernelCenterAction ω).ρ k.val ≅
      𝟭 (Center (CocycleVec (kernelCocycle ω))) :=
  canonicalInnerTrivialization ω k

instance canonicalKernelCenterTrivialization_monoidal (k : KillingKernel G) :
    NatTrans.IsMonoidal (canonicalKernelCenterTrivialization ω k).hom :=
  canonicalInnerTrivialization_monoidal ω k

lemma canonicalKernelCenterAction_rhoEq_app_f {g h : KillingExtension G} (e : g = h)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (((WeakAction.rhoEqIso (canonicalKernelCenterAction ω) e).hom.app Z).f) =
      eqToHom (congrArg (fun a => (canonicalKernelPush ω a).obj Z.1) e) := by
  cases e
  rfl

lemma canonicalKernelCenterAction_mul_inv_app_f (g h : KillingExtension G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    (((canonicalKernelCenterAction ω).mulIso g h).inv.app Z).f =
      (canonicalKernelPushMul ω g h).inv.app Z.1 := by
  have he : (Center.forget _).mapIso (((canonicalKernelCenterAction ω).mulIso g h).app Z) =
      (canonicalKernelPushMul ω g h).app Z.1 := by
    apply Iso.ext
    exact DrinfeldEquivalence.centerAction_mul_hom_app_f (canonicalKernelAction ω) g h Z
  exact congrArg Iso.inv he

/-- The actual equivariance law is precisely the standard kernel
conjugation law used by the genuine quotient construction. -/
theorem canonicalKernelCenterTrivialization_conjugation (g : KillingExtension G)
    (k : KillingKernel G) (Z : Center (CocycleVec (kernelCocycle ω))) :
    ((canonicalKernelCenterAction ω).ρ g).map
        ((canonicalKernelCenterTrivialization ω k).hom.app Z) =
      ((canonicalKernelCenterAction ω).mulIso g k.val).hom.app Z ≫
        (WeakAction.kernelComparison UniversalExtension.projection (canonicalKernelCenterAction ω)
          (canonicalKernelCenterTrivialization ω) (g*k.val) g
          (by rw [map_mul, show UniversalExtension.projection k.val = 1 from k.property,
            mul_one])).hom.app Z := by
  rw [WeakAction.kernelComparison_of_mul_raw UniversalExtension.projection
    (canonicalKernelCenterAction ω) (canonicalKernelCenterTrivialization ω)
    (conjugate g k) g (g*k.val) (canonicalConjugation_mul_eq g k).symm]
  apply Center.Hom.ext
  simp only [Center.comp_f, canonicalKernelCenterAction_rhoEq_app_f,
    canonicalKernelCenterAction_mul_inv_app_f]
  have ht := canonicalInnerTrivialization_conjugation ω g k Z
  rw [canonicalKernelPushConjugationIso_eq] at ht
  simpa only [canonicalKernelCenterTrivialization, canonicalKernelCenterAction,
    DrinfeldEquivalence.centerAction_rho_map_f, DrinfeldEquivalence.centerAction_mul_hom_app_f,
    canonicalKernelAction_mulIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    eqToIso.hom, eqToHom_app, Category.assoc] using ht.symm

end Paper18.Category.CrossedExtension
