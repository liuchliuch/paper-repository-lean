import Paper18.Category.CrossedExtensionActionCochain

/-! # Normalization from inverse pullback to canonical push conjugation -/
noncomputable section
universe u
namespace Paper18.Category.CrossedExtension
open Classical FiniteCohomologyKilling QuasiFusion
variable {G : Type u} [Group G] [Fintype G] (ω : FourCocycle G ℂˣ)

/-- The actual scalar changing the inverse-pullback convention to the
canonical push convention. -/
def innerNormalization (g : KillingExtension G) (k : KillingKernel G) : ℂˣ :=
  conjugationComparison ω g g⁻¹ k

@[simp] lemma innerNormalization_unit (k : KillingKernel G) :
    innerNormalization ω 1 k = 1 := by simp [innerNormalization]

@[simp] lemma innerNormalization_one (g : KillingExtension G) :
    innerNormalization ω g 1 = 1 := by simp [innerNormalization]

/-- The normalization preserves the actual tensorator, by the actual
multiplication-comparison identity at `(g,g⁻¹)`. -/
theorem innerNormalization_tensor (g : KillingExtension G) (k l : KillingKernel G) :
    (conjugationTensorator ω g⁻¹ k l)⁻¹ * innerNormalization ω g (k * l) =
      innerNormalization ω g k * innerNormalization ω g l *
        conjugationTensorator ω g (conjugate g⁻¹ k) (conjugate g⁻¹ l) := by
  have e := congrArg Additive.ofMul (conjugationComparison_tensor ω g g⁻¹ k l)
  simp only [mul_inv_cancel, conjugationTensorator_unit, one_mul, ofMul_mul] at e
  apply Additive.ofMul.injective
  simp only [innerNormalization, ofMul_mul, ofMul_inv]
  linear_combination (norm := abel) e

/-- The actual normalization also intertwines the actual multiplication
comparisons. No quotient action or comparison coherence is assumed. -/
theorem innerNormalization_comp (g h : KillingExtension G) (k : KillingKernel G) :
    conjugationComparison ω h⁻¹ g⁻¹ k * innerNormalization ω (g * h) k =
      innerNormalization ω g k * innerNormalization ω h (conjugate g⁻¹ k) *
        (conjugationComparison ω g h (conjugate (g * h)⁻¹ k))⁻¹ := by
  have e₁ := congrArg Additive.ofMul
    (conjugationComparison_assoc ω g h (h⁻¹ * g⁻¹) k)
  have e₂ := congrArg Additive.ofMul
    (conjugationComparison_assoc ω h h⁻¹ g⁻¹ k)
  have hm : h * (h⁻¹ * g⁻¹) = g⁻¹ := by group
  rw [hm] at e₁
  rw [mul_inv_cancel] at e₂
  simp only [conjugationComparison_one_left, one_mul, ofMul_mul, ofMul_one] at e₁ e₂
  apply Additive.ofMul.injective
  simp only [innerNormalization, mul_inv_rev, ofMul_mul, ofMul_inv]
  linear_combination (norm := abel) e₁ - e₂

end Paper18.Category.CrossedExtension
