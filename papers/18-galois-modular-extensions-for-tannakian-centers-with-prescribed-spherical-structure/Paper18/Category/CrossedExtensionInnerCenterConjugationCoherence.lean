import Paper18.Category.CrossedExtensionInnerCenterConjugationFunctor

/-! # The actual conjugation comparison and action multiplication -/
noncomputable section
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 200000
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerConjugationCoherenceFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

lemma canonicalConjugation_mul_eq (g : KillingExtension G) (k : KillingKernel G) :
    g * k.val = (conjugate g k).val * g := by
  simp [conjugate_val, mul_assoc]

/-- The component square of the explicitly constructed conjugation map
is the square of the actual action multiplication comparisons. -/
theorem canonicalKernelPushConjugationIso_mul (g : KillingExtension G) (k : KillingKernel G) :
    (canonicalKernelPushConjugationIso ω g k).hom ≫
        (canonicalKernelPushMul ω (conjugate g k).val g).hom =
      (canonicalKernelPushMul ω g k.val).hom ≫
        eqToHom (congrArg (canonicalKernelPush ω) (canonicalConjugation_mul_eq g k)) := by
  apply NatTrans.ext
  funext X
  apply GradedObject.hom_ext
  intro a
  change (canonicalKernelPushConjugationIso ω g k).hom.app X a ≫
      (canonicalKernelPushMul ω (conjugate g k).val g).hom.app X a =
    (canonicalKernelPushMul ω g k.val).hom.app X a ≫
      (eqToHom (congrArg (canonicalKernelPush ω) (canonicalConjugation_mul_eq g k))).app X a
  rw [canonicalKernelPushConjugationIso_hom_app,
    canonicalKernelPushMul_hom_app, canonicalKernelPushMul_hom_app,
    eqToHom_app, GradedObject.eqToHom_apply]
  simp only [Linear.smul_comp, Linear.comp_smul, smul_smul,
    Units.val_mul, eqToHom_trans]
  congr 1
  rw [← canonicalConjugation_mul_eq g k]
  simp only [← Units.val_mul]
  congr 1
  simp [mul_comm, mul_assoc]

/-- Transport in the group parameter preserves the constructed monoidal
functor structure. -/
theorem canonicalKernelPush_transport_monoidal {g h : KillingExtension G} (e : g = h) :
    NatTrans.IsMonoidal (eqToIso (congrArg (canonicalKernelPush ω) e)).hom := by
  subst h
  change NatTrans.IsMonoidal (𝟙 (canonicalKernelPush ω g))
  infer_instance

/-- The explicit conjugation comparison is precisely the composite of
the two multiplication comparisons and the group equality transport. -/
theorem canonicalKernelPushConjugationIso_eq (g : KillingExtension G) (k : KillingKernel G) :
    canonicalKernelPushConjugationIso ω g k =
      canonicalKernelPushMul ω g k.val ≪≫
        eqToIso (congrArg (canonicalKernelPush ω) (canonicalConjugation_mul_eq g k)) ≪≫
          (canonicalKernelPushMul ω (conjugate g k).val g).symm := by
  apply Iso.ext
  apply (cancel_mono (canonicalKernelPushMul ω (conjugate g k).val g).hom).1
  simpa only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    Iso.inv_hom_id, Category.comp_id, eqToIso.hom] using
      canonicalKernelPushConjugationIso_mul ω g k

/-- The actual conjugation comparison preserves the actual tensorators
and unit maps, by its multiplication-comparison description. -/
instance canonicalKernelPushConjugationIso_monoidal (g : KillingExtension G) (k : KillingKernel G) :
    NatTrans.IsMonoidal (canonicalKernelPushConjugationIso ω g k).hom := by
  haveI := canonicalKernelPush_transport_monoidal ω (canonicalConjugation_mul_eq g k)
  rw [canonicalKernelPushConjugationIso_eq]
  simp only [Iso.trans_hom, Iso.symm_hom]
  infer_instance

end Paper18.Category.CrossedExtension
