import Paper18.Category.CrossedExtensionInnerNormalizationCrossing
import Paper18.Category.CrossedExtensionInnerNormalizationComposition

/-! # Actual conjugation of the kernel line and its comparison scalars -/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
namespace Paper18.Category.CrossedExtension
open QuasiFusion FiniteCohomologyKilling PointedVec
variable {G : Type} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)
local instance innerCenterConjugationFintype : Fintype (KillingKernel G) := Fintype.ofFinite _

/-- Pullback conjugation carries the actual degree-`k` complex line to
the actual conjugated degree, with coefficient one. -/
lemma kernelLine_image_eq (g : KillingExtension G) (k : KillingKernel G) :
    (canonicalKernelPush ω g).obj (kernelLine ω k) = kernelLine ω (conjugate g k) := by
  classical
  funext a
  change kernelLine ω k (Additive.ofMul (conjugate g⁻¹ a.toMul)) =
    kernelLine ω (conjugate g k) a
  dsimp only [kernelLine, simpleObject, GradedObject.single]
  have h : Additive.ofMul (conjugate g⁻¹ a.toMul) = Additive.ofMul k ↔
      a = Additive.ofMul (conjugate g k) := by
    constructor
    · intro he
      have hh := congrArg (fun b : Additive (KillingKernel G) =>
        Additive.ofMul (conjugate g b.toMul)) he
      simpa using hh
    · intro he
      subst a
      simp
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact False.elim (h₂ (h.mp h₁))
  · exact False.elim (h₁ (h.mpr h₂))
  · rfl

/-- The canonical actual comparison of the image of a kernel line with
the line at its conjugated degree. -/
def kernelLineImageIso (g : KillingExtension G) (k : KillingKernel G) :
    (canonicalKernelPush ω g).obj (kernelLine ω k) ≅ kernelLine ω (conjugate g k) :=
  eqToIso (kernelLine_image_eq ω g k)

/-- The crossing comparison under conjugation is an actual identity
among the explicitly constructed primitive scalars. -/
theorem innerConjugation_scalar (g : KillingExtension G) (k b : KillingKernel G) :
    conjugationTensorator ω g k b *
        (conjugationTensorator ω g (conjugate k.val b) k)⁻¹ *
        (conjugationComparison ω g k.val b)⁻¹ *
        conjugationComparison ω (conjugate g k).val g b = 1 := by
  have he : (conjugate g k).val * g = g * k.val := by
    simp [conjugate, mul_assoc]
  apply Additive.ofMul.injective
  simp only [conjugationTensorator, conjugationComparison, he,
    conjugate_conjugate, ofMul_mul, ofMul_inv, ofMul_one]
  abel

end Paper18.Category.CrossedExtension
