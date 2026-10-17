import Paper18.Category.PointedRelativeCenterObstructionPentagon
import Paper18.Category.CrossedExtensionScalarAction

/-! # Actual kernel-conjugation coefficients from mixed cochain pentagons

These coefficients will be used in actual pullback functors and actual
natural isomorphisms, with their action coherence proved below.
-/
noncomputable section
open Classical CategoryTheory CategoryTheory.Category
namespace Paper18.Category.PointedRelativeCenterObstruction
open FiniteCohomologyKilling
variable {Γ G : Type} [Group Γ] [Fintype Γ] [Group G]
  (p : Γ →* G) (ψ : ThreeCochain Γ ℂˣ) (ω : FourCocycle G ℂˣ)
  (hψ : ∀ a b c d, dThree ψ.val a b c d = ω.val (p a) (p b) (p c) (p d))
include hψ

lemma kernelAction_mixed_scalar (a b c d : Γ)
    (hn : p a = 1 ∨ p b = 1 ∨ p c = 1 ∨ p d = 1) :
    ψ.val b c d * ψ.val a (b * c) d * ψ.val a b c =
      ψ.val (a * b) c d * ψ.val a b (c * d) := by
  have hd : dThree ψ.val a b c d = 1 := by
    rw [hψ]
    rcases hn with h | h | h | h <;> simp [h]
  calc
    _ = dThree ψ.val a b c d * (ψ.val (a * b) c d * ψ.val a b (c * d)) := by
      apply Additive.ofMul.injective
      simp only [dThree, ofMul_mul, ofMul_inv]
      abel
    _ = _ := by rw [hd, one_mul]

omit hψ in
/-- Inverse conjugation is the degree pullback for the standard left-action
composition order. -/
def kernelActionDegree (k : p.ker) (a : Γ) : Γ := k.val⁻¹ * a * k.val

omit hψ in
@[simp] lemma kernelActionDegree_one (a : Γ) : kernelActionDegree p 1 a = a := by
  simp [kernelActionDegree]

omit hψ in
@[simp] lemma kernelActionDegree_mul (k l : p.ker) (a : Γ) :
    kernelActionDegree p l (kernelActionDegree p k a) = kernelActionDegree p (k * l) a := by
  simp [kernelActionDegree, mul_assoc]

omit hψ in
lemma kernelActionDegree_commute (k : p.ker) (a : Γ) :
    k.val * kernelActionDegree p k a = a * k.val := by
  simp [kernelActionDegree, mul_assoc]

omit hψ in
@[simp] lemma kernelActionDegree_projection (k : p.ker) (a : Γ) :
    p (kernelActionDegree p k a) = p a := by
  have hk : p k.val = 1 := k.property
  simp [kernelActionDegree, hk]

omit hψ in
/-- The coefficient obtained by dragging a vector strand through two
neutral homogeneous lines. It is normalized because ψ is normalized. -/
def kernelActionScalar (k l : p.ker) (a : Γ) : ℂˣ :=
  ψ.val k.val (kernelActionDegree p k a) l.val * (ψ.val a k.val l.val)⁻¹ *
    (ψ.val k.val l.val (kernelActionDegree p (k * l) a))⁻¹

omit hψ in
@[simp] lemma kernelActionScalar_one_left (k : p.ker) (a : Γ) :
    kernelActionScalar p ψ 1 k a = 1 := by
  simp [kernelActionScalar]

omit hψ in
@[simp] lemma kernelActionScalar_one_right (k : p.ker) (a : Γ) :
    kernelActionScalar p ψ k 1 a = 1 := by
  simp [kernelActionScalar]

/-- Four actual mixed cochain pentagons prove the actual pullback-action
2-cocycle identity. No action-coherence premise is supplied. -/
lemma kernelActionScalar_assoc (k l m : p.ker) (a : Γ) :
    kernelActionScalar p ψ l m (kernelActionDegree p k a) *
      kernelActionScalar p ψ k (l * m) a =
    kernelActionScalar p ψ k l a * kernelActionScalar p ψ (k * l) m a := by
  have h₁ := kernelAction_mixed_scalar p ψ ω hψ a k.val l.val m.val
    (Or.inr (Or.inl k.property))
  have h₂ := kernelAction_mixed_scalar p ψ ω hψ k.val (kernelActionDegree p k a) l.val m.val
    (Or.inl k.property)
  have h₃ := kernelAction_mixed_scalar p ψ ω hψ k.val l.val
    (kernelActionDegree p (k * l) a) m.val (Or.inl k.property)
  have h₄ := kernelAction_mixed_scalar p ψ ω hψ k.val l.val m.val
    (kernelActionDegree p ((k * l) * m) a) (Or.inl k.property)
  have hc₁ : k.val * kernelActionDegree p k a = a * k.val := kernelActionDegree_commute p k a
  have hc₂ : l.val * kernelActionDegree p (k * l) a = kernelActionDegree p k a * l.val := by
    simpa only [kernelActionDegree_mul] using
      kernelActionDegree_commute p l (kernelActionDegree p k a)
  have hc₃ : m.val * kernelActionDegree p ((k * l) * m) a =
      kernelActionDegree p (k * l) a * m.val := by
    simpa only [kernelActionDegree_mul] using
      kernelActionDegree_commute p m (kernelActionDegree p (k * l) a)
  rw [hc₁] at h₂
  rw [hc₂] at h₃
  rw [hc₃] at h₄
  apply Additive.ofMul.injective
  simp only [kernelActionScalar, kernelActionDegree_mul, mul_assoc,
    Subgroup.coe_mul, ofMul_mul, ofMul_inv]
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e₃ := congrArg Additive.ofMul h₃
  have e₄ := congrArg Additive.ofMul h₄
  simp only [ofMul_mul, mul_assoc, Subgroup.coe_mul] at e₁ e₂ e₃ e₄
  linear_combination (norm := abel) e₁ - e₂ + e₃ - e₄

end Paper18.Category.PointedRelativeCenterObstruction
