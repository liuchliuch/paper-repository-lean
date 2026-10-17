import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import GeometricMedianCoresets.Basic
import GeometricMedianCoresets.FeatureMap
import GeometricMedianCoresets.CostIdentity
import GeometricMedianCoresets.Variance
import GeometricMedianCoresets.GeometricInequalities
import GeometricMedianCoresets.Stability
import GeometricMedianCoresets.Comparison
import GeometricMedianCoresets.LowerBoundAlgebra
import GeometricMedianCoresets.NegativeType

/-!
# Paper correspondence: compatibility exports for the deterministic components

Re-exports the original closed deterministic interfaces. The complete probability,
actual Gaussian/L1 feature maps, distinct-point lower bound and threshold results
are imported by the root library and indexed by their precise names in `publication.json`.

Proved here:

* `lemma_2_2`        — cost-difference identity (5)–(6)
* `lemma_2_6`        — stability from relative comparison
* `lemma_2_6_gap`    — scalar gap of Lemma 2.6
* `prop_2_4_det`     — deterministic form of (9)
* `eq_11_*`          — geometric inequalities (11)
* `lower_bound_*`    — algebraic inequalities of §3
* `cor_4_1_skeleton` — negative-type stability skeleton
-/

noncomputable section

open scoped BigOperators RealInnerProductSpace

namespace GeometricMedianCoresets
namespace Paper

/-- Lemma 2.2, eq. (6). -/
theorem lemma_2_2 {X : Type*} (S : SquaredMetric X)
    {n m : ℕ} (hn : n ≠ 0) (hm : m ≠ 0)
    (P : Dataset X n) (Q : Dataset X m) (x y : X) :
    S.toDist.delta P Q x y = 2 * ⟪S.Φ x - S.Φ y, S.v Q - S.v P⟫ :=
  S.delta_eq_inner hn hm P Q x y

/-- Geometric inequality (11): averaged triangle. -/
theorem eq_11_triangle {X : Type*} (D : Dist X) {n : ℕ} (hn : 0 < n)
    (P : Dataset X n) (x y : X) :
    D.d x y ≤ D.cost P x + D.cost P y :=
  triangle_avg D hn P x y

/-- Geometric inequality (11): optimality of the infimum. -/
theorem eq_11_optimality {X : Type*} (D : Dist X) {n : ℕ}
    (P : Dataset X n) (x y : X) :
    2 * D.optimum P ≤ D.cost P x + D.cost P y :=
  two_opt_le D P x y

/-- Remark 2.5 scalar identity. -/
theorem remark_2_5 {m : ℝ} (hm : m ≠ 0) {R : ℝ} :
    R / m = 2 * (R / (2 * m)) := by
  field_simp

/-- Lemma 2.6 gap identity. -/
theorem lemma_2_6_gap (ε : ℝ) :
    (1 + 17 * ε) * (1 - ε) - (1 + 11 * ε + 2 * ε ^ 2) = ε * (5 - 19 * ε) :=
  lemma26_gap_identity ε

/-- Deterministic skeleton of Proposition 2.4. -/
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
  prop24_deterministic hm hopt hmean hmean0 htri h2opt hs hd

/-- Lemma 2.6 as a stable-coreset statement. -/
theorem lemma_2_6 {X : Type*} (D : Dist X) {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    {μ : X} (hμ : D.IsGeometricMedian P μ)
    (hΔ : ∀ x y : X, |D.delta P Q x y| ≤ ε * (D.cost P x + D.cost P y))
    (href : D.cost Q μ ≤ 10 * D.cost P μ) :
    IsStableCoreset D P Q ε (17 * ε) :=
  lemma_2_6_stable D P Q hε hε' hμ hΔ href

/-- Section 3: population preference gap. -/
theorem lower_bound_pref_gap {ε θ pA pB : ℝ}
    (hε : 0 < ε) (hε' : ε ≤ 1/100)
    (hθlo : 10 * ε ≤ θ) (hθhi : θ ≤ 11 * ε)
    (hp : pA = (1 - θ) / 2 ∧ pB = (1 + θ) / 2) :
    pB - (1 + 17 * ε) * pA ≥ (3/2) * ε + 85 * ε ^ 2 :=
  LowerBound.pref_gap hε hε' hθlo hθhi hp

/-- Section 3: majority reversal. -/
theorem lower_bound_majority {ε ρ : ℝ}
    (hε : 0 < ε) (_hε' : ε < 1/4)
    (hρok : ρ * (3 + ε) ≤ ε) :
    1/2 + ρ ≤ (1 + ε) * (1/2 * (1 - ρ)) :=
  LowerBound.majority_reversal hε hρok

/-- Corollary 4.1 deterministic skeleton. -/
theorem cor_4_1_skeleton {X : Type*} (S : NegativeTypeMetric X)
    {n m : ℕ} (P : Dataset X n) (Q : Dataset X m)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    {μ : X} (hμ : S.toDist.IsGeometricMedian P μ)
    (hΔ : ∀ x y : X,
      |S.toDist.delta P Q x y| ≤ ε * (S.toDist.cost P x + S.toDist.cost P y))
    (href : S.toDist.cost Q μ ≤ 10 * S.toDist.cost P μ) :
    IsStableCoreset S.toDist P Q ε (17 * ε) :=
  S.cor41_stable_skeleton P Q hε hε' hμ hΔ href

end Paper
end GeometricMedianCoresets
