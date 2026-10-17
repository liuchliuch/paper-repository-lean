import Paper18.Category.QuasiFusionCocycle

/-! # Actual conjugation tensorators from the finite fourth-cocycle primitive

The primitive is generally not a third cocycle on the extension. Every
pentagon with a kernel entry does hold, and these actual mixed pentagons
give the tensorator for conjugation on the genuine kernel fusion category.
-/
noncomputable section
universe u
namespace Paper18.Category.CrossedExtension
open Classical FiniteCohomologyKilling QuasiFusion
variable {G : Type u} [Group G] [Fintype G]

/-- Actual conjugation preserves the actual kernel of the killing extension. -/
def conjugate (g : KillingExtension G) (k : KillingKernel G) : KillingKernel G :=
  ⟨g * k.val * g⁻¹, by
    change (g * k.val * g⁻¹).quotient = 1
    have hk : k.val.quotient = 1 := k.property
    have hi : g⁻¹.quotient = g.quotient⁻¹ := UniversalExtension.projection.map_inv g
    simp only [UniversalExtension.mul_quotient, hk, mul_one, hi, mul_inv_cancel]⟩

@[simp] lemma conjugate_val (g : KillingExtension G) (k : KillingKernel G) :
    (conjugate g k).val = g * k.val * g⁻¹ := rfl

@[simp] lemma conjugate_one (g : KillingExtension G) : conjugate g 1 = 1 := by
  apply Subtype.ext
  simp [conjugate]

@[simp] lemma conjugate_mul (g : KillingExtension G) (k l : KillingKernel G) :
    conjugate g (k * l) = conjugate g k * conjugate g l := by
  apply Subtype.ext
  simp [conjugate, mul_assoc]

@[simp] lemma conjugate_cancel (g : KillingExtension G) (k : KillingKernel G) :
    conjugate g⁻¹ (conjugate g k) = k := by
  apply Subtype.ext
  simp [conjugate, mul_assoc]

/-- Conjugation is an actual group automorphism of the finite kernel. -/
def conjugationAut (g : KillingExtension G) : MulAut (KillingKernel G) where
  toFun := conjugate g
  invFun := conjugate g⁻¹
  left_inv := conjugate_cancel g
  right_inv k := by simpa only [inv_inv] using conjugate_cancel g⁻¹ k
  map_mul' := conjugate_mul g

variable (ω : FourCocycle G ℂˣ)

/-- The actual primitive satisfies every mixed pentagon with a kernel entry. -/
lemma primitive_mixed_pentagon (a b c d : KillingExtension G)
    (h : a.quotient = 1 ∨ b.quotient = 1 ∨ c.quotient = 1 ∨ d.quotient = 1) :
    ω.finitePrimitive.val b c d * ω.finitePrimitive.val a (b * c) d *
        ω.finitePrimitive.val a b c =
      ω.finitePrimitive.val (a * b) c d * ω.finitePrimitive.val a b (c * d) := by
  have hd : dThree ω.finitePrimitive.val a b c d = 1 := by
    rw [ω.finitePrimitive_spec]
    rcases h with h | h | h | h <;> simp [h]
  calc
    _ = dThree ω.finitePrimitive.val a b c d *
        (ω.finitePrimitive.val (a * b) c d * ω.finitePrimitive.val a b (c * d)) := by
      apply Additive.ofMul.injective
      simp only [dThree, ofMul_mul, ofMul_inv]
      abel
    _ = _ := by rw [hd, one_mul]

/-- The actual scalar tensorator for conjugation of kernel-graded lines. -/
def conjugationTensorator (g : KillingExtension G) (k l : KillingKernel G) : ℂˣ :=
  ω.finitePrimitive.val g k.val l.val *
    ω.finitePrimitive.val (conjugate g k).val (conjugate g l).val g *
      (ω.finitePrimitive.val (conjugate g k).val g l.val)⁻¹

@[simp] lemma conjugationTensorator_one_left (g : KillingExtension G) (k : KillingKernel G) :
    conjugationTensorator ω g 1 k = 1 := by
  simp [conjugationTensorator]

@[simp] lemma conjugationTensorator_one_right (g : KillingExtension G) (k : KillingKernel G) :
    conjugationTensorator ω g k 1 = 1 := by
  simp [conjugationTensorator]

/-- Actual monoidal associativity of the conjugation tensorator, proved by
four mixed pentagons of the explicitly constructed primitive. -/
theorem conjugationTensorator_coherence (g : KillingExtension G) (k l m : KillingKernel G) :
    conjugationTensorator ω g k l * conjugationTensorator ω g (k * l) m *
        (kernelCocycle ω).val k l m =
      (kernelCocycle ω).val (conjugate g k) (conjugate g l) (conjugate g m) *
        conjugationTensorator ω g l m * conjugationTensorator ω g k (l * m) := by
  have h₁ := primitive_mixed_pentagon ω g k.val l.val m.val (Or.inr (Or.inl k.property))
  have h₂ := primitive_mixed_pentagon ω (conjugate g k).val g l.val m.val
    (Or.inl (conjugate g k).property)
  have h₃ := primitive_mixed_pentagon ω (conjugate g k).val (conjugate g l).val g m.val
    (Or.inl (conjugate g k).property)
  have h₄ := primitive_mixed_pentagon ω (conjugate g k).val (conjugate g l).val
    (conjugate g m).val g (Or.inl (conjugate g k).property)
  have hkg : (conjugate g k).val * g = g * k.val := by simp [conjugate, mul_assoc]
  have hlg : (conjugate g l).val * g = g * l.val := by simp [conjugate, mul_assoc]
  have hmg : (conjugate g m).val * g = g * m.val := by simp [conjugate, mul_assoc]
  rw [hkg, ← hlg] at h₂
  rw [hlg, ← hmg] at h₃
  apply Additive.ofMul.injective
  simp only [conjugationTensorator, kernelCocycle, conjugate_mul, Subgroup.coe_mul,
    ofMul_mul, ofMul_inv]
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e₃ := congrArg Additive.ofMul h₃
  have e₄ := congrArg Additive.ofMul h₄
  simp only [ofMul_mul] at e₁ e₂ e₃ e₄
  apply sub_eq_zero.mp
  calc
    _ =
      (Additive.ofMul (ω.finitePrimitive.val k.val l.val m.val) +
        Additive.ofMul (ω.finitePrimitive.val g (k.val * l.val) m.val) +
        Additive.ofMul (ω.finitePrimitive.val g k.val l.val) -
        (Additive.ofMul (ω.finitePrimitive.val (g * k.val) l.val m.val) +
          Additive.ofMul (ω.finitePrimitive.val g k.val (l.val * m.val)))) -
      (Additive.ofMul (ω.finitePrimitive.val g l.val m.val) +
        Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val
          ((conjugate g l).val * g) m.val) +
        Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val g l.val) -
        (Additive.ofMul (ω.finitePrimitive.val (g * k.val) l.val m.val) +
          Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val g (l.val * m.val)))) +
      (Additive.ofMul (ω.finitePrimitive.val (conjugate g l).val g m.val) +
        Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val (g * l.val) m.val) +
        Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val (conjugate g l).val g) -
        (Additive.ofMul (ω.finitePrimitive.val ((conjugate g k).val * (conjugate g l).val) g m.val) +
          Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val (conjugate g l).val
            ((conjugate g m).val * g)))) -
      (Additive.ofMul (ω.finitePrimitive.val (conjugate g l).val (conjugate g m).val g) +
        Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val
          ((conjugate g l).val * (conjugate g m).val) g) +
        Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val (conjugate g l).val
          (conjugate g m).val) -
        (Additive.ofMul (ω.finitePrimitive.val ((conjugate g k).val * (conjugate g l).val)
          (conjugate g m).val g) +
          Additive.ofMul (ω.finitePrimitive.val (conjugate g k).val (conjugate g l).val
            ((conjugate g m).val * g)))) := by rw [hlg]; abel
    _ = 0 := by rw [sub_eq_zero.mpr e₁, sub_eq_zero.mpr e₂,
      sub_eq_zero.mpr e₃, sub_eq_zero.mpr e₄]; simp

/-- The inverse tensorator has the orientation required by pullback of
graded objects along conjugation. -/
theorem conjugationTensorator_inverse_coherence
    (g : KillingExtension G) (k l m : KillingKernel G) :
    (conjugationTensorator ω g k l)⁻¹ * (conjugationTensorator ω g (k * l) m)⁻¹ *
        (kernelCocycle ω).val (conjugate g k) (conjugate g l) (conjugate g m) =
      (kernelCocycle ω).val k l m * (conjugationTensorator ω g l m)⁻¹ *
        (conjugationTensorator ω g k (l * m))⁻¹ := by
  have h := congrArg Additive.ofMul (conjugationTensorator_coherence ω g k l m)
  simp only [ofMul_mul] at h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  calc
    _ = -(Additive.ofMul (conjugationTensorator ω g k l) +
        Additive.ofMul (conjugationTensorator ω g (k * l) m) +
        Additive.ofMul ((kernelCocycle ω).val k l m)) +
      Additive.ofMul ((kernelCocycle ω).val k l m) +
      Additive.ofMul ((kernelCocycle ω).val (conjugate g k) (conjugate g l) (conjugate g m)) := by
      abel
    _ = _ := by rw [h]; abel

end Paper18.Category.CrossedExtension
