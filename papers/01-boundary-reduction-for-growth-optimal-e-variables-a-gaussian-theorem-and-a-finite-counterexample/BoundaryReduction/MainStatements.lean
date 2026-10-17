/-
Copyright (c) 2026. Paper-to-Lean statement specifications for
"Boundary reduction for growth-optimal e-variables: a Gaussian theorem
and a finite counterexample".

Retains the early finite and geometric interfaces. Full Gaussian and
nine-point theorems are proved in sibling modules and mapped to source
results in `publication.json` and `SEMANTIC_AUDIT.md`.
-/
import BoundaryReduction.FirstExit
import BoundaryReduction.FiniteKL
import BoundaryReduction.Numerical
import BoundaryReduction.GrowBound

open Real Set
open scoped Topology

namespace BoundaryReduction

/-! ## Lemma 2.1 — GROW–information upper bound

Paper: `GROW(C) ≤ I(C)` for every nonempty `C ⊆ M`.
Finite-alphabet engine of the proof is proved below. -/
theorem lemma_2_1_finite
    {α : Type*} [Fintype α]
    {p₀ r : FinProb α} {S : α → ℝ}
    (hp₀ : ∀ y, 0 < p₀.w y) (hr : ∀ y, 0 < r.w y)
    (hS : ∀ y, 0 < S y) (hm : 0 < FinProb.expect p₀ S) :
    FinProb.expect r (fun y => log (S y))
      ≤ FinProb.klPos r p₀ + log (FinProb.expect p₀ S) :=
  FinProb.grow_info_core_of_pos hp₀ hr hS hm

/-! ## Lemma 4.3 — First-exit propagation

Paper: if `B` is open, `0 ∈ B`, `g` is raywise convex, `g 0 ≤ c ≤ inf_{∂B} g`,
then `g μ ≥ c` for every `μ ∉ B`. -/
theorem lemma_4_3 {d : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin d))} {g : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ}
    (hB_open : IsOpen B) (hB_zero : (0 : EuclideanSpace ℝ (Fin d)) ∈ B)
    (hg : RaywiseConvex g) (hg0 : g 0 ≤ c)
    (hboundary : ∀ r ∈ frontier B, c ≤ g r)
    {μ : EuclideanSpace ℝ (Fin d)} (hμ : μ ∉ B) : c ≤ g μ :=
  first_exit_propagation hB_open hB_zero hg hg0 hboundary hμ

theorem lemma_4_3_ball {d : ℕ}
    (g : EuclideanSpace ℝ (Fin d) → ℝ) (c r₀ : ℝ) (hr₀ : 0 < r₀)
    (hg : RaywiseConvex g) (hg0 : g 0 ≤ c)
    (hboundary : ∀ r, ‖r‖ = r₀ → c ≤ g r) :
    ∀ μ, r₀ ≤ ‖μ‖ → c ≤ g μ :=
  first_exit_ball g c r₀ hr₀ hg hg0 hboundary

/-! ## Theorem 4.1 — analytic engine

Once a boundary mixture yields `f(0) ≤ c ≤ inf_{∂B} f` with `f` raywise
convex, the global inequality `f(μ) ≥ c` holds on the exterior. This is
exactly `lemma_4_3` and needs no star-shapedness. The construction of the
unique Borel minimiser, Gaussian translation convexity of `f_W`, and the
GROW optimality chain are proved in the Gaussian production modules; see
`Gaussian.theorem_4_1_covariance` and `SEMANTIC_AUDIT.md`. -/
theorem theorem_4_1_first_exit_engine {d : ℕ}
    {B : Set (EuclideanSpace ℝ (Fin d))}
    {f : EuclideanSpace ℝ (Fin d) → ℝ} {c : ℝ}
    (hB_open : IsOpen B) (hB_zero : (0 : EuclideanSpace ℝ (Fin d)) ∈ B)
    (hf : RaywiseConvex f) (hf0 : f 0 ≤ c)
    (hboundary : ∀ r ∈ frontier B, c ≤ f r) :
    ∀ μ ∉ B, c ≤ f μ :=
  fun μ hμ => lemma_4_3 hB_open hB_zero hf hf0 hboundary hμ

/-! ## Theorem 3.1 — nine-point counterexample, numerical shell

The uniform separator constants of Section 3.1 and Appendix A are proved
in `BoundaryReduction.Numerical`. The exponential-family tilt construction
and the information-theoretic separation `I(M\B) < 2·10⁻¹⁵ < 7·10⁻¹² < I(∂B)`
are proved in `NinePoint.theorem_3_1_mean`. -/
theorem theorem_3_1_constants :
    (0 : ℝ) < Numerical.ε ∧
    Numerical.ε < 2 * (10 : ℝ) ^ (-15 : ℤ) ∧
    Numerical.r₀ = (10 : ℝ) ^ (-2 : ℤ) ∧
    Numerical.ρ ^ 2 = 8 / 25 ∧
    (13 / 100 : ℝ) < 2 * Numerical.ρ - 1 := by
  exact ⟨Numerical.ε_pos, Numerical.ε_lt_two, Numerical.r₀_eq_inv,
    Numerical.ρ_sq, Numerical.gamma_exposure_gap⟩

end BoundaryReduction
