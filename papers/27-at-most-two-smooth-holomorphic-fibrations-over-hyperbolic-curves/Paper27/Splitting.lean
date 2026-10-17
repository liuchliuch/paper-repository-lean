import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The fibrewise linear algebra in (4) and (6)

These results prove the averaging and affine-combination calculations used in
§3. They do not construct a neighbourhood, a group action on a surface, or a
holomorphic subbundle. Those geometric assertions remain separate obligations.
-/

noncomputable section
open scoped BigOperators

namespace Paper27.Splitting

variable {G V W : Type*} [Group G] [Fintype G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- The average of the translates of a linear splitting, as in equation (4). -/
def average (ρ : G →* V ≃ₗ[ℂ] V) (σ : W →ₗ[ℂ] V) : W →ₗ[ℂ] V :=
  (Fintype.card G : ℂ)⁻¹ • ∑ g : G, (ρ g).toLinearMap.comp σ

@[simp] theorem average_apply (ρ : G →* V ≃ₗ[ℂ] V) (σ : W →ₗ[ℂ] V) (w : W) :
    average ρ σ w = (Fintype.card G : ℂ)⁻¹ • ∑ g : G, ρ g (σ w) := by
  simp [average, LinearMap.sum_apply]

/-- All translates are splittings when the projection is preserved by the action. -/
theorem average_is_splitting (ρ : G →* V ≃ₗ[ℂ] V) (π : V →ₗ[ℂ] W)
    (σ : W →ₗ[ℂ] V) (hπ : ∀ g v, π (ρ g v) = π v)
    (hσ : ∀ w, π (σ w) = w) (w : W) : π (average ρ σ w) = w := by
  have hcard : (Fintype.card G : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [average_apply, map_sum, hπ, hσ, ← Nat.cast_smul_eq_nsmul ℂ,
    smul_smul]

/-- Reindexing the finite sum makes the average invariant. -/
theorem average_invariant (ρ : G →* V ≃ₗ[ℂ] V) (σ : W →ₗ[ℂ] V) (g : G) (w : W) :
    ρ g (average ρ σ w) = average ρ σ w := by
  simp only [average_apply, map_smul, map_sum]
  congr 1
  calc
    ∑ h : G, ρ g (ρ h (σ w)) = ∑ h : G, ρ (g * h) (σ w) := by
      congr 1
      funext h
      rw [map_mul, LinearEquiv.mul_apply]
    _ = ∑ h : G, ρ h (σ w) :=
      Fintype.sum_equiv (Equiv.mulLeft g) _ _ (fun _ => rfl)

/-- Equation (6) preserves a splitting because the affine weights sum to one. -/
theorem affine_is_splitting (π : V →ₗ[ℂ] W) (σ₂ σ₃ : W →ₗ[ℂ] V)
    (a : ℂ) (ha : a ≠ 1) (h₂ : ∀ w, π (σ₂ w) = w) (h₃ : ∀ w, π (σ₃ w) = w)
    (w : W) : π (((a - 1)⁻¹ • (a • σ₃ - σ₂)) w) = w := by
  have hne : a - 1 ≠ 0 := sub_ne_zero.mpr ha
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub, h₂, h₃]
  have heq : a • w - w = (a - 1) • w := by rw [sub_smul, one_smul]
  rw [heq, smul_smul, inv_mul_cancel₀ hne, one_smul]

/-- At a point of the fixed curve, the normal eigenvalue is not one. -/
theorem fixed_normal_component_zero {ζ : ℂ} (hζ : ζ ≠ 1) (v : ℂ × ℂ)
    (hv : (v.1, ζ * v.2) = v) : v.2 = 0 := by
  have hs : ζ * v.2 = v.2 := congrArg Prod.snd hv
  have hz : (ζ - 1) * v.2 = 0 := by linear_combination hs
  exact (mul_eq_zero.mp hz).resolve_left (sub_ne_zero.mpr hζ)

/-- An invariant vector mapping to `w` under `dr` lies in the tangent line of D. -/
theorem fixed_splitting_tangent {ζ w : ℂ} (hζ : ζ ≠ 1) (v : ℂ × ℂ)
    (hv : (v.1, ζ * v.2) = v) (hπ : v.1 = w) : v = (w, 0) := by
  exact Prod.ext hπ (fixed_normal_component_zero hζ v hv)

end Paper27.Splitting
