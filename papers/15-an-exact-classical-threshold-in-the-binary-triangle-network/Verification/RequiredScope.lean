import Paper15

/-!
Independent statement-and-proof wrappers for all seven numbered results.
The statements keep the paper's quantifiers and hypotheses. The Comparator
challenge is isolated in Verification.Challenge; this module contains only
positive wrappers and is included in the final full-scope build.
-/
namespace P15Required
open Paper15 MeasureTheory

/-- Theorem 1, upper bound for every measurable classical triangle model. -/
theorem theorem_1 (M : TriangleModel)
    (h1 : M.aggregate.M1 = 0) (h3 : M.aggregate.M3 = 0) :
    M.aggregate.M2 ≤ tStar := Paper15.theorem1_sharp_bound M h1 h3

/-- Theorem 1, attainment. -/
theorem theorem_1_attainment :
    ∃ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 ∧
      (detMoments' T qx qy qz).M2 = tStar ∧
      (detMoments' T qx qy qz).M3 = 0 := Paper15.theorem1_attained

/-- Corollary 2 for the one-parameter family in its stated domain. -/
theorem corollary_2 (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    IsTriangleLocal t ↔ t ≤ tStar := Paper15.corollary2_iff t ht0 ht1

/-- Lemma 3, arbitrary bounded measurable map, prescribed full-measure set. -/
theorem lemma_3 {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsProbabilityMeasure μ]
    {d : ℕ} {g : α → EuclideanSpace ℝ (Fin d)}
    (hg : Measurable g) (hb : ∃ C : ℝ, ∀ x, ‖g x‖ ≤ C)
    (t : Set α) (ht : ∀ᵐ x ∂μ, x ∈ t) :
    ∃ (n : ℕ) (_ : n ≤ d + 1) (pts : Fin n → α) (w : Fin n → ℝ),
      (∀ i, pts i ∈ t) ∧ (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      (∑ i, w i • g (pts i) = ∫ x, g x ∂μ) :=
  Paper15.lemma3_bounded_measurable hg hb t ht

/-- Lemma 4, ternary deterministic maximum dominates ALL classical models. -/
theorem lemma_4 :
    ∃ (T : DetTriangle) (qx qy qz : Simplex2),
      (detMoments' T qx qy qz).M1 = 0 ∧
      (detMoments' T qx qy qz).M3 = 0 ∧
      ∀ M : TriangleModel, M.aggregate.M1 = 0 → M.aggregate.M3 = 0 →
        M.aggregate.M2 ≤ (detMoments' T qx qy qz).M2 := Paper15.lemma4_general_reduction

/-- Lemma 5, the complete orbit gap including boundary source laws. -/
theorem lemma_5 (T : DetTriangle) (hT : ¬ inExceptionalOrbit T) :
    GapHolds T := Paper15.lemma5_certified_gap T hT

/-- Lemma 6, actual partial derivatives of the moments (18). -/
theorem lemma_6 {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) :
    ¬ ∃ α β : ℝ, (α ≠ 0 ∨ β ≠ 0) ∧
      (∀ i, α * deriv (fun r => (momentsOf (Function.update x i r) y).M1) (x i) +
        β * deriv (fun r => (momentsOf (Function.update x i r) y).M3) (x i) = 0) ∧
      (∀ i, α * deriv (fun r => (momentsOf x (Function.update y i r)).M1) (y i) +
        β * deriv (fun r => (momentsOf x (Function.update y i r)).M3) (y i) = 0) :=
  Paper15.lemma6_derivative_independent hx hy

/-- Lemma 7, interior constrained stationary point (actual derivatives). -/
theorem lemma_7 {x y : Fin 3 → ℝ}
    (hx : ∀ i, 0 < x i) (hy : ∀ i, 0 < y i) (hz : ∀ i, x i + y i < 1)
    (hstat : IsExceptionalStationary x y) :
    x 0 = x 1 ∧ x 1 = x 2 ∧ y 0 = y 1 ∧ y 1 = y 2 :=
  Paper15.lemma7_stationary hx hy hz hstat

end P15Required
