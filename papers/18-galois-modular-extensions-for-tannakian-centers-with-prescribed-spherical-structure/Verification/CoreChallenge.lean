import Paper18.Fusion.TensorFunctor
import Mathlib.Data.ZMod.Basic

/-! Independent specifications of the verified algebraic core only.
These statements do not assert the paper's actual-category main theorem.
Placeholders are confined to this Comparator challenge, which solutions
must not import. -/

open Paper18
namespace P18Core

theorem dominant {ι κ : Type} [Fintype ι] [Fintype κ]
    {U : FusionBasis ι} {V : FusionBasis κ}
    (F : FusionMap U V) (hU : U.Integral) : V.Integral := by
  sorry

theorem equivariant {ι κ : Type} [Fintype ι] [Fintype κ]
    {C : FusionBasis ι} {E : FusionBasis κ}
    (M : EquivariantDimensionModel C E) : E.Integral ↔ C.Integral := by
  sorry

theorem two_coboundary (lam : ZMod 2 → ZMod 2 → ℂˣ)
    (h0 : ∀ y, lam 0 y = 1) (h1 : ∀ x, lam x 0 = 1) :
    ∃ μ : ZMod 2 → ℂˣ, μ 0 = 1 ∧
      ∀ x y, μ x * μ y * (μ (x + y))⁻¹ = lam x y := by
  sorry

theorem four_coboundary (ω : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ)
    (hω : ∀ x y z w, x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0 → ω x y z w = 1) :
    ∃ ψ : ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ,
      (∀ x y z, x = 0 ∨ y = 0 ∨ z = 0 → ψ x y z = 1) ∧
      ∀ x y z w, ψ y z w * (ψ (x + y) z w)⁻¹ * ψ x (y + z) w *
        (ψ x y (z + w))⁻¹ * ψ x y z = ω x y z w := by
  sorry

end P18Core
