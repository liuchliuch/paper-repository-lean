/-
Copyright (c) 2026. Affine slices, the lifted constraint (CP), and
exchangeability for finite de Finetti approximation with componentwise
constraints.
-/
import Paper06.Basic

open Real Set BigOperators
open scoped Classical

namespace Paper06

/-- The affine slice `F = {q : Γ q.w = η}` of the simplex. -/
def AffineSlice (α : Type*) [Fintype α]
    (Γ : (α → ℝ) → ℝ) (η : ℝ) : Set (FinProb α) :=
  {q | Γ q.w = η}

theorem mem_affineSlice {α : Type*} [Fintype α] {Γ : (α → ℝ) → ℝ} {η : ℝ}
    {q : FinProb α} (h : Γ q.w = η) : q ∈ AffineSlice α Γ η :=
  h

/-- One-site marginal of a two-site law. -/
def marg1 {α : Type*} [Fintype α] (P : FinProb (α × α)) : FinProb α where
  w z := ∑ a, P.w (z, a)
  nonneg := by
    intro z
    exact Finset.sum_nonneg (fun a _ => P.nonneg _)
  sum_eq_one := by
    have key : ∑ z : α, ∑ a : α, P.w (z, a) = ∑ x : α × α, P.w x :=
      (Fintype.sum_prod_type' (fun z a => P.w (z, a))).symm
    rw [key, P.sum_eq_one]

/-- Lifted constraint (CP) at the second coordinate of a two-site law:
`Γ(P₂(z, ·)) = P₁(z) · η` and the second-site marginal matches `P₁`. -/
def CP2 {α : Type*} [Fintype α]
    (Γ : (α → ℝ) → ℝ) (η : ℝ) (P₂ : FinProb (α × α)) (P₁ : FinProb α) : Prop :=
  (∀ z : α, Γ (fun a => P₂.w (z, a)) = P₁.w z * η) ∧
  marg1 P₂ = P₁

/-- Exchangeability of a law on `α × α`. -/
def Exchangeable2 {α : Type*} [Fintype α] (P : FinProb (α × α)) : Prop :=
  ∀ x y : α, P.w (x, y) = P.w (y, x)

/-- Linear constraint map. -/
structure LinΓ (α : Type*) [Fintype α] where
  f : (α → ℝ) → ℝ
  map_add : ∀ p q : α → ℝ, f (fun y => p y + q y) = f p + f q
  map_smul : ∀ (c : ℝ) (p : α → ℝ), f (fun y => c * p y) = c * f p

/-- **Lemma 2.1 (Posterior preservation), two-site form.**
If `P₂` satisfies (CP) with target `η` and `P₁ = marg1 P₂`, then for every
`z` with `P₁ z > 0` the posterior of the second site given the first equals
`η` after applying the linear map `Γ`. -/
theorem lemma_2_1_linear {α : Type*} [Fintype α]
    (Γ : LinΓ α) (η : ℝ)
    (P₂ : FinProb (α × α)) (P₁ : FinProb α)
    (hCP : CP2 Γ.f η P₂ P₁) :
    ∀ z : α, 0 < P₁.w z →
      Γ.f (fun a => P₂.w (z, a) / P₁.w z) = η := by
  intro z hz
  have hγ : Γ.f (fun a => P₂.w (z, a)) = P₁.w z * η := hCP.1 z
  have hscale : (fun a => P₂.w (z, a) / P₁.w z)
      = (fun a => (P₁.w z)⁻¹ * P₂.w (z, a)) := by
    funext a
    rw [div_eq_mul_inv, mul_comm]
  rw [hscale]
  have hrew : Γ.f (fun a => (P₁.w z)⁻¹ * P₂.w (z, a))
      = (P₁.w z)⁻¹ * Γ.f (fun a => P₂.w (z, a)) := by
    have hsmul := Γ.map_smul (P₁.w z)⁻¹ (fun a => P₂.w (z, a))
    simpa using hsmul
  rw [hrew, hγ]
  have hne : P₁.w z ≠ 0 := ne_of_gt hz
  field_simp [hne]

end Paper06
