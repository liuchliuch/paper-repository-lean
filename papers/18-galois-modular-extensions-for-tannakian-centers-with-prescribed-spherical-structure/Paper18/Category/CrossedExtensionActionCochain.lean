import Paper18.Category.CrossedExtensionCochain

/-! # Actual multiplication comparisons for conjugation tensor functors -/
noncomputable section
universe u
namespace Paper18.Category.CrossedExtension
open Classical FiniteCohomologyKilling QuasiFusion
variable {G : Type u} [Group G] [Fintype G]

@[simp] lemma conjugate_conjugate (g h : KillingExtension G) (k : KillingKernel G) :
    conjugate g (conjugate h k) = conjugate (g * h) k := by
  apply Subtype.ext
  simp [conjugate, mul_assoc]

@[simp] lemma conjugate_unit (k : KillingKernel G) : conjugate 1 k = k := by
  apply Subtype.ext
  simp [conjugate]

lemma conjugate_commute (g : KillingExtension G) (k : KillingKernel G) :
    (conjugate g k).val * g = g * k.val := by simp [conjugate, mul_assoc]

variable (ω : FourCocycle G ℂˣ)

@[simp] lemma conjugationTensorator_unit (k l : KillingKernel G) :
    conjugationTensorator ω 1 k l = 1 := by simp [conjugationTensorator]

/-- The actual normalized scalar comparing a pair of conjugations with
conjugation by their product. -/
def conjugationComparison (g h : KillingExtension G) (k : KillingKernel G) : ℂˣ :=
  ω.finitePrimitive.val g h k.val *
    ω.finitePrimitive.val (conjugate (g * h) k).val g h *
      (ω.finitePrimitive.val g (conjugate h k).val h)⁻¹

@[simp] lemma conjugationComparison_one_left (g : KillingExtension G) (k : KillingKernel G) :
    conjugationComparison ω 1 g k = 1 := by simp [conjugationComparison]
@[simp] lemma conjugationComparison_one_right (g : KillingExtension G) (k : KillingKernel G) :
    conjugationComparison ω g 1 k = 1 := by simp [conjugationComparison]
@[simp] lemma conjugationComparison_unit (g h : KillingExtension G) :
    conjugationComparison ω g h 1 = 1 := by simp [conjugationComparison]

/-- The multiplication comparison is actually compatible with the
conjugation tensorators; six proved mixed pentagons give the equation. -/
theorem conjugationComparison_tensor (g h : KillingExtension G) (k l : KillingKernel G) :
    conjugationTensorator ω (g * h) k l * conjugationComparison ω g h (k * l) =
      conjugationTensorator ω g (conjugate h k) (conjugate h l) *
        conjugationTensorator ω h k l * conjugationComparison ω g h k *
        conjugationComparison ω g h l := by
  have h₁ := primitive_mixed_pentagon ω g h k.val l.val (Or.inr (Or.inr (Or.inl k.property)))
  have h₂ := primitive_mixed_pentagon ω g (conjugate h k).val h l.val
    (Or.inr (Or.inl (conjugate h k).property))
  have h₃ := primitive_mixed_pentagon ω g (conjugate h k).val (conjugate h l).val h
    (Or.inr (Or.inl (conjugate h k).property))
  have h₄ := primitive_mixed_pentagon ω (conjugate (g * h) k).val g h l.val
    (Or.inl (conjugate (g * h) k).property)
  have h₅ := primitive_mixed_pentagon ω (conjugate (g * h) k).val g (conjugate h l).val h
    (Or.inl (conjugate (g * h) k).property)
  have h₆ := primitive_mixed_pentagon ω (conjugate (g * h) k).val
    (conjugate (g * h) l).val g h (Or.inl (conjugate (g * h) k).property)
  have hkg : (conjugate (g * h) k).val * g = g * (conjugate h k).val := by
    simpa only [conjugate_conjugate] using conjugate_commute g (conjugate h k)
  have hlg : (conjugate (g * h) l).val * g = g * (conjugate h l).val := by
    simpa only [conjugate_conjugate] using conjugate_commute g (conjugate h l)
  rw [conjugate_commute h k, ← hkg] at h₂
  rw [conjugate_commute h l, ← hkg] at h₃
  rw [hkg] at h₄
  rw [hkg, conjugate_commute h l, ← hlg] at h₅
  rw [hlg] at h₆
  apply Additive.ofMul.injective
  simp only [conjugationTensorator, conjugationComparison, conjugate_conjugate,
    conjugate_mul, Subgroup.coe_mul, ofMul_mul, ofMul_inv]
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e₃ := congrArg Additive.ofMul h₃
  have e₄ := congrArg Additive.ofMul h₄
  have e₅ := congrArg Additive.ofMul h₅
  have e₆ := congrArg Additive.ofMul h₆
  simp only [ofMul_mul] at e₁ e₂ e₃ e₄ e₅ e₆
  simp only [hkg, hlg] at e₁ e₂ e₃ e₄ e₅ e₆
  linear_combination (norm := abel) -e₁ + e₂ - e₃ - e₄ + e₅ - e₆

/-- Tensor compatibility in the pullback orientation of the actual action. -/
theorem conjugationComparison_tensor_pullback
    (g h : KillingExtension G) (k l : KillingKernel G) :
    (conjugationTensorator ω h k l)⁻¹ *
        (conjugationTensorator ω g (conjugate h k) (conjugate h l))⁻¹ *
        conjugationComparison ω g h (k * l) =
      conjugationComparison ω g h k * conjugationComparison ω g h l *
        (conjugationTensorator ω (g * h) k l)⁻¹ := by
  have e := congrArg Additive.ofMul (conjugationComparison_tensor ω g h k l)
  simp only [ofMul_mul] at e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  linear_combination (norm := abel) e

/-- The actual multiplication comparisons obey the action associativity
coherence, again by actual mixed pentagons of the actual primitive. -/
theorem conjugationComparison_assoc (g h j : KillingExtension G) (k : KillingKernel G) :
    conjugationComparison ω g h (conjugate j k) * conjugationComparison ω (g * h) j k =
      conjugationComparison ω h j k * conjugationComparison ω g (h * j) k := by
  have h₁ := primitive_mixed_pentagon ω g h j k.val
    (Or.inr (Or.inr (Or.inr k.property)))
  have h₂ := primitive_mixed_pentagon ω g h (conjugate j k).val j
    (Or.inr (Or.inr (Or.inl (conjugate j k).property)))
  have h₃ := primitive_mixed_pentagon ω g (conjugate (h * j) k).val h j
    (Or.inr (Or.inl (conjugate (h * j) k).property))
  have h₄ := primitive_mixed_pentagon ω (conjugate (g * (h * j)) k).val g h j
    (Or.inl (conjugate (g * (h * j)) k).property)
  have hkh : (conjugate (h * j) k).val * h = h * (conjugate j k).val := by
    simpa only [conjugate_conjugate] using conjugate_commute h (conjugate j k)
  have hkg : (conjugate (g * (h * j)) k).val * g = g * (conjugate (h * j) k).val := by
    simpa only [conjugate_conjugate] using conjugate_commute g (conjugate (h * j) k)
  rw [conjugate_commute j k] at h₂
  rw [hkh] at h₃
  rw [hkg] at h₄
  apply Additive.ofMul.injective
  simp only [conjugationComparison, conjugate_conjugate, mul_assoc, ofMul_mul, ofMul_inv]
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e₃ := congrArg Additive.ofMul h₃
  have e₄ := congrArg Additive.ofMul h₄
  simp only [ofMul_mul, mul_assoc] at e₁ e₂ e₃ e₄
  linear_combination (norm := abel) -e₁ + e₂ - e₃ + e₄

end Paper18.Category.CrossedExtension
