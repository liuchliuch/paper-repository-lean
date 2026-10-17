import Paper18.Category.CrossedExtensionInnerCenterKernel
import Paper18.Category.CrossedExtensionInnerNormalizationProductCenter
import Paper18.Category.WeakActionQuotientStandardUnit

/-! # Genuine quotient action on the actual kernel Drinfeld center -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
attribute [local instance] innerCenterKernelFintype

/-- The actual line-product diagram gives the standard kernel product law. -/
theorem canonicalKernelCenterTrivialization_mul (k l : KillingKernel G)
    (Z : Center (CocycleVec (kernelCocycle ω))) :
    ((canonicalKernelCenterAction ω).mulIso k.val l.val).hom.app Z ≫
        (canonicalKernelCenterTrivialization ω (k*l)).hom.app Z =
      ((canonicalKernelCenterAction ω).ρ k.val).map
        ((canonicalKernelCenterTrivialization ω l).hom.app Z) ≫
        (canonicalKernelCenterTrivialization ω k).hom.app Z := by
  apply Center.Hom.ext
  simpa only [Center.comp_f, canonicalKernelCenterTrivialization, canonicalKernelCenterAction,
    DrinfeldEquivalence.centerAction_rho_map_f, DrinfeldEquivalence.centerAction_rho_obj_fst,
    DrinfeldEquivalence.centerAction_mul_hom_app_f, Functor.comp_obj,
    canonicalKernelAction_mulIso, canonicalKernelAction_rho] using
      canonicalInnerTrivialization_mul_map ω k l Z

/-- Every standard kernel law is derived from the actual homogeneous-line
crossings, not supplied as a premise of the quotient action. -/
def canonicalKernelCenterStandard :
    WeakAction.StandardKernelTrivialization
      (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
      (canonicalKernelCenterAction ω) :=
  WeakAction.StandardKernelTrivialization.ofMulConjugation
    (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
    (canonicalKernelCenterAction ω) (canonicalKernelCenterTrivialization ω)
    (canonicalKernelCenterTrivialization_mul ω)
    (by
      intro g k Z
      -- Normalize the generic kernel comparison before exposing concrete
      -- homogeneous-line maps and their already proved conjugation diagram.
      rw [WeakAction.kernelComparison_of_mul_raw UniversalExtension.projection
        (canonicalKernelCenterAction ω) (canonicalKernelCenterTrivialization ω)
        (conjugate g k) g (g*k.val) (canonicalConjugation_mul_eq g k).symm]
      apply Center.Hom.ext
      simp only [Center.comp_f, canonicalKernelCenterAction_rhoEq_app_f,
        canonicalKernelCenterAction_mul_inv_app_f]
      have ht := canonicalInnerTrivialization_conjugation ω g k Z
      rw [canonicalKernelPushConjugationIso_eq] at ht
      simpa only [canonicalKernelCenterTrivialization, canonicalKernelCenterAction,
        DrinfeldEquivalence.centerAction_rho_map_f,
        DrinfeldEquivalence.centerAction_mul_hom_app_f,
        canonicalKernelAction_mulIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
        eqToIso.hom, eqToHom_app, Category.assoc] using ht.symm)

instance canonicalKernelCenterStandard_monoidal :
    (canonicalKernelCenterStandard ω).IsMonoidal (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
      (canonicalKernelCenterAction ω) where
  trivialization_monoidal k := canonicalKernelCenterTrivialization_monoidal ω k

/-- Actual action normalization transports the derived coherent kernel
trivializations back to the original primitive action. -/
def kernelCenterStandard :
    WeakAction.StandardKernelTrivialization (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) (kernelCenterAction ω) :=
  (canonicalKernelCenterStandard ω).ofActionIso (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
    (kernelCenterActionNormalization ω)

instance kernelCenterStandard_monoidal :
    (kernelCenterStandard ω).IsMonoidal (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) (kernelCenterAction ω) := by
  unfold kernelCenterStandard
  infer_instance

/-- The actual `G`-action on the actual Drinfeld center of kernel-graded
vector spaces. Its multiplication and unit constraints are constructed
by genuine quotient descent of the proved kernel trivializations. -/
def quotientCenterAction : WeakAction G (Center (CocycleVec (kernelCocycle ω))) :=
  (kernelCenterStandard ω).descend (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) (kernelCenterAction ω)
    UniversalExtension.projection_surjective

instance quotientCenterAction_rho_monoidal (g : G) :
    ((quotientCenterAction ω).ρ g).Monoidal := by
  unfold quotientCenterAction
  infer_instance

instance quotientCenterAction_isMonoidal : (quotientCenterAction ω).IsMonoidal := by
  unfold quotientCenterAction
  infer_instance

instance quotientCenterAction_rho_additive (g : G) :
    ((quotientCenterAction ω).ρ g).Additive := by
  unfold quotientCenterAction
  infer_instance

instance quotientCenterAction_rho_linear (g : G) :
    ((quotientCenterAction ω).ρ g).Linear ℂ := by
  unfold quotientCenterAction
  infer_instance

instance quotientCenterAction_rho_braided (g : G) :
    ((quotientCenterAction ω).ρ g).Braided := by
  change ((kernelCenterAction ω).ρ
    ((WeakAction.chosenQuotientSection (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))
      UniversalExtension.projection_surjective).lift g)).Braided
  infer_instance

/-- The original finite-extension action is actually coherently
monoidally isomorphic to the pullback of the constructed quotient action. -/
def quotientCenterDescentIso :
    WeakAction.ActionIso (kernelCenterAction ω)
      (WeakAction.pullback (quotientCenterAction ω) (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G)))) :=
  (kernelCenterStandard ω).descentIso (UniversalExtension.projection (G := G) (R := ZMod (Fintype.card G))) (kernelCenterAction ω)
    UniversalExtension.projection_surjective

instance quotientCenterDescentIso_monoidal : (quotientCenterDescentIso ω).IsMonoidal := by
  unfold quotientCenterDescentIso
  infer_instance

end Paper18.Category.CrossedExtension
