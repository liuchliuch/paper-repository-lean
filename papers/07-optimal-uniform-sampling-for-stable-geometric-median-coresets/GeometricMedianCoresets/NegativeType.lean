import Mathlib.Data.Real.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import GeometricMedianCoresets.Basic
import GeometricMedianCoresets.FeatureMap
import GeometricMedianCoresets.StableOnGood
import GeometricMedianCoresets.Stability

/-!
# Negative-type metrics (paper §4)

A metric space is of negative type when distances are squared Hilbert
distances (eq. (20)). Under that representation the same algebra as §2
applies. Corollary 4.1 reduces stability to Lemma 2.6 for `d`-costs.

The actual Gaussian representation, coordinatewise `L₂` map and attained
Euclidean/l1 medians are proved in the sibling feature-map and metric
modules. The general negative-type result below retains the stated
attained-median premise.
-/

noncomputable section

namespace GeometricMedianCoresets

/-- Negative-type representation: `d(x,y) = ‖Ψ(x) - Ψ(y)‖^2` for a map into a
real Hilbert space, together with the metric triangle inequality. -/
structure NegativeTypeMetric (X : Type*) where
  /-- Ambient Hilbert space. -/
  H : Type
  [normed : NormedAddCommGroup H]
  [hilbert : InnerProductSpace ℝ H]
  /-- Underlying metric. -/
  d : X → X → ℝ
  /-- Feature map. -/
  Ψ : X → H
  /-- Squared Hilbert distance realizes `d` (eq. (20)). -/
  dist_sq : ∀ x y : X, ‖Ψ x - Ψ y‖ ^ 2 = d x y
  nonneg : ∀ x y, 0 ≤ d x y
  symm : ∀ x y, d x y = d y x
  triangle : ∀ x y z, d x y ≤ d x z + d z y

attribute [instance] NegativeTypeMetric.normed NegativeTypeMetric.hilbert

namespace NegativeTypeMetric

variable {X : Type*} (S : NegativeTypeMetric X)

def toDist : Dist X where
  d := S.d
  nonneg := S.nonneg
  symm := S.symm
  triangle := S.triangle

def toSquaredMetric : SquaredMetric X where
  H := S.H
  d := S.d
  Φ := S.Ψ
  dist_sq := S.dist_sq
  triangle := S.triangle

/-- Deterministic stability skeleton of Corollary 4.1: same scalar argument
as Lemma 2.6, applied to `d`-costs of a negative-type metric. -/
theorem cor41_stable_skeleton {n m : ℕ}
    (P : Dataset X n) (Q : Dataset X m)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    {μ : X} (hμ : S.toDist.IsGeometricMedian P μ)
    (hΔ : ∀ x y : X,
      |S.toDist.delta P Q x y| ≤ ε * (S.toDist.cost P x + S.toDist.cost P y))
    (href : S.toDist.cost Q μ ≤ 10 * S.toDist.cost P μ) :
    IsStableCoreset S.toDist P Q ε (17 * ε) :=
  lemma_2_6_stable S.toDist P Q hε hε' hμ hΔ href

end NegativeTypeMetric

end GeometricMedianCoresets

namespace GeometricMedianCoresets.NegativeTypeMetric
attribute [local instance] Classical.propDecidable

/-- Corollary 4.1, with the uniform law over the actual `m`-subsets. -/
theorem cor41_uniform_stable {X : Type*} (S : NegativeTypeMetric X) {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (P : Dataset X n)
    (μ : X) (hμ : S.toDist.IsGeometricMedian P μ)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε < 1/4)
    (hmsize : ⌈20 / (ε * ε)⌉₊ ≤ m) :
    (((Finset.univ : Finset (Fin n)).powersetCard m).filter
      (fun I => IsStableCoreset S.toDist P (indexedSample P I) ε (17 * ε))).card
      / (n.choose m : ℝ) ≥ 4 / 5 :=
  uniform_stable_4_5_ceil S.toSquaredMetric hn hm hmn P μ hμ hε hε' hmsize

end GeometricMedianCoresets.NegativeTypeMetric
