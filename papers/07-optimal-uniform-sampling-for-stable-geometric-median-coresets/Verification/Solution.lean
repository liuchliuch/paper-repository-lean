import GeometricMedianCoresets.Paper

/-!
# Proofs of the separately reviewed paper statements

Does not import the challenge or its independent model. Each declaration has
the fixed interface of `Verification/Challenge.lean` and is witnessed by a
closed proof from the mathematical library.
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace
namespace GeometricMedianCoresets.Challenge

/-- Lemma 2.2 (cost-difference identity), eq. (6). -/
theorem lemma_2_2 {X : Type*} (S : SquaredMetric X)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Dataset X n) (Q : Dataset X m) (x y : X) :
    S.toDist.delta P Q x y = 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫ :=
  S.delta_eq_inner hn hm P Q x y

/-- Lemma 2.6 (stability from relative comparison). -/
theorem lemma_2_6 {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    {μ : X} (hμ : D.IsGeometricMedian P μ)
    (hΔ : ∀ x y : X, |D.delta P Q x y| ≤ ε * (D.cost P x + D.cost P y))
    (href : D.cost Q μ ≤ 10 * D.cost P μ) :
    IsStableCoreset D P Q ε (17 * ε) :=
  GeometricMedianCoresets.Paper.lemma_2_6 D P Q hε hε' hμ hΔ href

/-- Proposition 2.4, deterministic form of eq. (9). -/
theorem prop_2_4_det
    {m opt dist_xy fp_x fp_y mean_err : ℝ}
    (hm : 0 < m) (hopt : 0 ≤ opt)
    (hmean : mean_err ≤ 10 * opt / m)
    (hmean0 : 0 ≤ mean_err)
    (htri : dist_xy ≤ fp_x + fp_y)
    (h2opt : 2 * opt ≤ fp_x + fp_y)
    (hs : 0 ≤ fp_x + fp_y)
    (hd : 0 ≤ dist_xy) :
    2 * Real.sqrt (dist_xy * mean_err)
      ≤ Real.sqrt (20 / m) * (fp_x + fp_y) :=
  GeometricMedianCoresets.Paper.prop_2_4_det hm hopt hmean hmean0 htri h2opt hs hd

/-- Geometric inequality (11). -/
theorem eq_11_triangle {X : Type*} (D : Dist X) {n : ℕ} (hn : 0 < n)
    (P : Dataset X n) (x y : X) :
    D.d x y ≤ D.cost P x + D.cost P y :=
  GeometricMedianCoresets.Paper.eq_11_triangle D hn P x y

/-- Geometric inequality (11). -/
theorem eq_11_optimality {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (x y : X) :
    2 * D.optimum P ≤ D.cost P x + D.cost P y :=
  GeometricMedianCoresets.Paper.eq_11_optimality D P x y

/-- Lemma 2.6 scalar gap identity. -/
theorem lemma_2_6_gap (ε : ℝ) :
    (1 + 17 * ε) * (1 - ε) - (1 + 11 * ε + 2 * ε ^ 2) = ε * (5 - 19 * ε) :=
  GeometricMedianCoresets.Paper.lemma_2_6_gap ε

/-- Section 3: population preference gap. -/
theorem lower_bound_pref_gap {ε θ pA pB : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1/100)
    (hθlo : 10 * ε ≤ θ) (hθhi : θ ≤ 11 * ε)
    (hp : pA = (1 - θ) / 2 ∧ pB = (1 + θ) / 2) :
    pB - (1 + 17 * ε) * pA ≥ (3/2) * ε + 85 * ε ^ 2 :=
  GeometricMedianCoresets.Paper.lower_bound_pref_gap hε hε' hθlo hθhi hp

/-- Section 3: majority reversal. -/
theorem lower_bound_majority {ε ρ : ℝ}
    (hε : 0 < ε) (hε' : ε < 1/4)
    (hρok : ρ * (3 + ε) ≤ ε) :
    1/2 + ρ ≤ (1 + ε) * (1/2 * (1 - ρ)) :=
  GeometricMedianCoresets.Paper.lower_bound_majority hε hε' hρok

end GeometricMedianCoresets.Challenge
