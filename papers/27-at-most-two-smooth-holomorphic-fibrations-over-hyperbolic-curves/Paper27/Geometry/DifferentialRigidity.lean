import Paper27.Geometry.Objects
import Mathlib.Analysis.Normed.Field.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Differential calculations along a ramification component

The covectors and tangent maps are genuine complex-linear maps. These lemmas
supply the proportionality uniqueness, metric comparison at an intersection,
and normal-factorization calculation in Proposition 2.4 and Lemma 3.1.
-/
noncomputable section
namespace Paper27.Geometry.DifferentialRigidity

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- A covector vanishing on the kernel of a surjective covector is its scalar
multiple. The coefficient is nonzero when the second covector is surjective. -/
theorem exists_nonzero_scalar (l₁ l₂ : V →ₗ[ℂ] ℂ)
    (h₁ : Function.Surjective l₁) (h₂ : Function.Surjective l₂)
    (hker : ∀ v, l₁ v = 0 → l₂ v = 0) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ v, l₂ v = a * l₁ v := by
  obtain ⟨e, he⟩ := h₁ 1
  have hfactor : ∀ v, l₂ v = l₂ e * l₁ v := by
    intro v
    have hv : l₁ (v - l₁ v • e) = 0 := by simp [he]
    have hv₂ := hker _ hv
    simp only [map_sub, map_smul, smul_eq_mul] at hv₂
    linear_combination hv₂
  refine ⟨l₂ e, ?_, hfactor⟩
  intro hz
  obtain ⟨v, hv⟩ := h₂ 1
  have := hfactor v
  rw [hz, zero_mul, hv] at this
  exact one_ne_zero this

/-- The nonzero differential of the first fibration determines a graph's slope
uniquely, including when a normalization tangent itself vanishes. -/
theorem scalar_unique (l : V →ₗ[ℂ] ℂ) (hl : Function.Surjective l)
    {a b : ℂ} (h : ∀ v, a * l v = b * l v) : a = b := by
  obtain ⟨v, hv⟩ := hl 1
  simpa [hv] using h v

/-- Equality of two proportional rank-one metrics on one nonzero tangent
forces equality on the entire tangent space. -/
theorem proportional_metrics_equal (l : V →ₗ[ℂ] ℂ) (a : ℂ)
    (ρ σ : ℝ) (e : V) (he : l e ≠ 0)
    (hmetric : ρ * ‖l e‖ ^ 2 = σ * ‖a * l e‖ ^ 2) :
    ∀ v, ρ * ‖l v‖ ^ 2 = σ * ‖a * l v‖ ^ 2 := by
  have hn : ‖l e‖ ^ 2 ≠ 0 := pow_ne_zero _ (norm_ne_zero_iff.mpr he)
  have hfactor : ρ = σ * ‖a‖ ^ 2 := by
    apply (mul_right_cancel₀ hn)
    simpa only [norm_mul, mul_pow, ← mul_assoc] using hmetric
  intro v
  rw [hfactor, norm_mul, mul_pow]
  ring

/-- The correction β=df₃−(d(f₃|D)/d(f₁|D))df₁ vanishes on the tangent
line. Thus its factorization through the normal quotient is justified. -/
theorem beta_annihilates_tangent (l₁ l₃ : V →ₗ[ℂ] ℂ) (t : ℂ →ₗ[ℂ] V)
    (c₁ c₃ : ℂ) (hc₁ : c₁ ≠ 0)
    (h₁ : ∀ z, l₁ (t z) = c₁ * z) (h₃ : ∀ z, l₃ (t z) = c₃ * z) :
    ∀ z, (l₃ - (c₃ / c₁) • l₁) (t z) = 0 := by
  intro z
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, h₁, h₃, smul_eq_mul]
  field_simp
  <;> ring

/-- The coefficient of dr₂∧dr₃ in the paper is n(a−1). Its exact order
therefore rules out a=1; this is not a new hypothesis on the fibration. -/
theorem leading_coefficient_ne_one {n : ℕ} {a : ℂ}
    (hlead : (n : ℂ) * (a - 1) ≠ 0) : a ≠ 1 := by
  intro ha
  apply hlead
  simp [ha]

end Paper27.Geometry.DifferentialRigidity
