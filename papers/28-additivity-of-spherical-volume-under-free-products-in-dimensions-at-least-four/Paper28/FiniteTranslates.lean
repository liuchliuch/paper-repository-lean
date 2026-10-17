import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.Cofinite
import Mathlib.Data.Finsupp.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Pointwise.Finset.Basic

/-! Actual group-coordinate finiteness used in S3.p7 and S5.SS1.p5.
These statements do not require a current or a quotient-space abstraction. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter

variable {G : Type*} [Group G] [DecidableEq G]

/-- All translations which can make two prescribed finite supports meet. -/
def overlapTranslations (F F' : Finset G) : Finset G :=
  (F ×ˢ F').image fun p => p.1 * p.2⁻¹

theorem mem_overlapTranslations (F F' : Finset G) (γ : G) :
    γ ∈ overlapTranslations F F' ↔ ∃ x ∈ F, ∃ y ∈ F', x = γ * y := by
  constructor
  · intro h
    obtain ⟨⟨x, y⟩, hxy, heq⟩ := Finset.mem_image.mp h
    obtain ⟨hx, hy⟩ := Finset.mem_product.mp hxy
    refine ⟨x, hx, y, hy, ?_⟩
    rw [← heq]
    simp
  · rintro ⟨x, hx, y, hy, hxy⟩
    apply Finset.mem_image.mpr
    refine ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, ?_⟩
    simpa [hxy]

/-- The set of relevant translates is finite, with no local compactness assumption. -/
theorem finite_overlapTranslations (F F' : Finset G) :
    {γ : G | ∃ x ∈ F, ∃ y ∈ F', x = γ * y}.Finite := by
  have heq : {γ : G | ∃ x ∈ F, ∃ y ∈ F', x = γ * y} =
      (overlapTranslations F F' : Set G) := by
    ext γ
    exact (mem_overlapTranslations F F' γ).symm
  rw [heq]
  exact Finset.finite_toSet _

/-- A real matrix coefficient of the left regular representation for finite
support vectors, after the change of variable x = γ*y. -/
def finiteRegularCoefficient (u v : G →₀ ℝ) (γ : G) : ℝ :=
  ∑ y ∈ v.support, u (γ * y) * v y

theorem finiteRegularCoefficient_eq_zero (u v : G →₀ ℝ) (γ : G)
    (hγ : γ ∉ overlapTranslations u.support v.support) :
    finiteRegularCoefficient u v γ = 0 := by
  apply Finset.sum_eq_zero
  intro y hy
  have hzero : u (γ * y) = 0 := by
    by_contra h
    have hu : γ * y ∈ u.support := Finsupp.mem_support_iff.mpr h
    exact hγ ((mem_overlapTranslations _ _ _).mpr ⟨γ * y, hu, y, hy, rfl⟩)
  rw [hzero, zero_mul]

/-- Finite-support coefficients vanish outside a finite set, the first
step of the decay argument in S5.Ex25. -/
theorem finiteRegularCoefficient_eventually_zero (u v : G →₀ ℝ) :
    ∀ᶠ γ in Filter.cofinite, finiteRegularCoefficient u v γ = 0 := by
  apply Filter.mem_of_superset (Finset.finite_toSet (overlapTranslations u.support v.support)).compl_mem_cofinite
  intro γ hγ
  exact finiteRegularCoefficient_eq_zero u v γ hγ

end Paper28
