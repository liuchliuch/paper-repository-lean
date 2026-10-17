import Paper18.Results.Integrality
import Paper18.Results.AppendixA

/-! Solutions to independently specified algebraic-core contracts.
The Comparator challenge is not imported. -/

open Paper18
namespace P18Core

theorem dominant {ι κ : Type} [Fintype ι] [Fintype κ]
    {U : FusionBasis ι} {V : FusionBasis κ}
    (F : FusionMap U V) (hU : U.Integral) : V.Integral :=
  Paper18.lemma3_1_dominant F hU

theorem equivariant {ι κ : Type} [Fintype ι] [Fintype κ]
    {C : FusionBasis ι} {E : FusionBasis κ}
    (M : EquivariantDimensionModel C E) : E.Integral ↔ C.Integral :=
  M.integral_iff

theorem two_coboundary (lam : ZMod 2 → ZMod 2 → ℂˣ)
    (h0 : ∀ y, lam 0 y = 1) (h1 : ∀ x, lam x 0 = 1) :
    ∃ μ : ZMod 2 → ℂˣ, μ 0 = 1 ∧
      ∀ x y, μ x * μ y * (μ (x + y))⁻¹ = lam x y :=
  Paper18.lemmaA_1_cohomology' lam h0 h1

theorem four_coboundary (ω : ZMod 2 → ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ)
    (hω : ∀ x y z w, x = 0 ∨ y = 0 ∨ z = 0 ∨ w = 0 → ω x y z w = 1) :
    ∃ ψ : ZMod 2 → ZMod 2 → ZMod 2 → ℂˣ,
      (∀ x y z, x = 0 ∨ y = 0 ∨ z = 0 → ψ x y z = 1) ∧
      ∀ x y z w, ψ y z w * (ψ (x + y) z w)⁻¹ * ψ x (y + z) w *
        (ψ x y (z + w))⁻¹ * ψ x y z = ω x y z w := by
  obtain ⟨ψ, hn, hψ⟩ := Paper18.normalizedFour_is_coboundary ω hω
  refine ⟨ψ, hn, ?_⟩
  intro x y z w
  exact congrFun (congrFun (congrFun (congrFun hψ x) y) z) w

end P18Core
