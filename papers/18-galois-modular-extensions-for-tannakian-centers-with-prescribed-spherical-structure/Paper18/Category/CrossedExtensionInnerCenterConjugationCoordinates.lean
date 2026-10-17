import Paper18.Category.CrossedExtensionInnerCenterConjugationFunctor

/-! # Actual source coordinates and scalar cancellation for conjugation -/
noncomputable section
set_option maxHeartbeats 2000000
open Classical CategoryTheory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerConjugationCoordinatesFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

lemma conjugation_regrade_inverse_apply (g : KillingExtension G)
    (a : Additive (KillingKernel G)) :
    (conjugationAut g⁻¹).toAdditive.symm a = Additive.ofMul (conjugate g a.toMul) := by
  change Additive.ofMul (conjugate (g⁻¹)⁻¹ a.toMul) = _
  rw [inv_inv]

/-- The actual tensorator and action-comparison coefficients cancel in
the output coordinate of the conjugation crossing. -/
theorem innerConjugation_scalar_regrade (g : KillingExtension G) (k : KillingKernel G)
    (c : Additive (KillingKernel G)) :
    let e := (conjugationAut g⁻¹).toAdditive
    let f := (conjugationAut k.val⁻¹).toAdditive
    conjugationTensorator ω g
        (conjugate g⁻¹ (Additive.ofMul (conjugate g k)).toMul)
        (conjugate g⁻¹ (e.symm (f c)).toMul) *
      (conjugationTensorator ω g (conjugate g⁻¹ (e.symm c).toMul)
        (conjugate g⁻¹ (Additive.ofMul (conjugate g k)).toMul))⁻¹ *
      ((conjugationComparison ω g k.val (conjugate (g*k.val)⁻¹ (e.symm c).toMul))⁻¹ *
        conjugationComparison ω (conjugate g k).val g
          (conjugate (g*k.val)⁻¹ (e.symm c).toMul)) = 1 := by
  dsimp only
  have hi : conjugate (g*k.val)⁻¹
      (((conjugationAut g⁻¹).toAdditive.symm c).toMul) =
      (((conjugationAut k.val⁻¹).toAdditive c).toMul) := by
    rw [conjugation_regrade_inverse_apply]
    apply Subtype.ext
    change (g*k.val)⁻¹ * (g*c.toMul.val*g⁻¹) * ((g*k.val)⁻¹)⁻¹ =
      k.val⁻¹*c.toMul.val*(k.val⁻¹)⁻¹
    group
  have hc : conjugate k.val (((conjugationAut k.val⁻¹).toAdditive c).toMul) = c.toMul := by
    change conjugate k.val (conjugate k.val⁻¹ c.toMul) = _
    simp only [conjugate_conjugate, mul_inv_cancel, conjugate_unit]
  have h := innerConjugation_scalar ω g k
    (((conjugationAut k.val⁻¹).toAdditive c).toMul)
  rw [hi]
  simp only [conjugation_regrade_inverse_apply, toMul_ofMul, conjugate_cancel]
  simpa only [hc, mul_assoc] using h

end Paper18.Category.CrossedExtension
