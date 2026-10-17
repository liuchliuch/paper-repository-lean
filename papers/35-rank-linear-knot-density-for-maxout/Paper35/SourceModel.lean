import Paper35.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.EMetricSpace.BoundedVariation
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! Explicit source objects and contracts for the distribution-free theorems.
These definitions are mathematical statements, not postulated theorems. In
particular, no crossing or visibility estimate is included as a model field. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace Paper35.Source

abbrev Space (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Candidate (d : ℕ) := Space d × ℝ

/-- A finite, positive-length arclength parameterization; its length is total
variation in the Euclidean metric. -/
structure Probe (d : ℕ) where
  curve : ℝ → Space d
  length : ℝ
  length_pos : 0 < length
  lipschitz : LipschitzOnWith 1 curve (Icc 0 length)
  arclength : eVariationOn curve (Icc 0 length) = ENNReal.ofReal length

/-- The actual conditional-density assumptions (2.4)-(2.5). -/
structure WeightedModel (d : ℕ) where
  weights : Measure (Space d)
  probability : IsProbabilityMeasure weights
  g : Space d → ℝ → ℝ≥0∞
  measurable_g : Measurable (Function.uncurry g)
  normalized_g : ∀ᵐ w ∂weights, ∫⁻ b, g w b = 1
  b₀ : Space d → ℝ≥0
  measurable_b₀ : Measurable b₀
  bound : ∀ᵐ w ∂weights, ∀ b, g w b ≤ b₀ w
  average_pos : 0 < ∫⁻ w, (b₀ w : ℝ≥0∞) ∂weights
  average_finite : (∫⁻ w, (b₀ w : ℝ≥0∞) ∂weights) < ∞

namespace WeightedModel
variable {d K : ℕ}

def average (m : WeightedModel d) : ℝ≥0∞ := ∫⁻ w, (m.b₀ w : ℝ≥0∞) ∂m.weights

def tilted (m : WeightedModel d) : Measure (Space d) :=
  m.weights.withDensity (fun w => (m.b₀ w : ℝ≥0∞) / m.average)

/-- Conditional sampling, expressed without any probability-zero conditioning. -/
def joint (m : WeightedModel d) : Measure (Candidate d) :=
  (m.weights.prod volume).withDensity (fun θ => m.g θ.1 θ.2)

def iid (m : WeightedModel d) (K : ℕ) : Measure (Fin K → Candidate d) :=
  Measure.pi (fun _ => m.joint)

def scores (p : Probe d) (θ : Fin K → Candidate d) : Fin K → ℝ → ℝ :=
  fun j s => inner ℝ (θ j).1 (p.curve s) + (θ j).2

def expectedCount (m : WeightedModel d) (K : ℕ) (p : Probe d) : ℝ≥0∞ :=
  expectedSwitchCount (m.iid K) (scores p) p.length

def directionalGini (m : WeightedModel d) (u : Space d) : ℝ≥0∞ :=
  ∫⁻ w, ∫⁻ w', ENNReal.ofReal (|inner ℝ u (w - w')|) ∂m.tilted ∂m.tilted

def projectedMean (m : WeightedModel d) (u : Space d) : ℝ :=
  ∫ w, inner ℝ u w ∂m.tilted

/-- The covariance quadratic form `uᵀ Σ̃ u`, defined from the tilted law. -/
def projectedVariance (m : WeightedModel d) (u : Space d) : ℝ :=
  ∫ w, (inner ℝ u w - m.projectedMean u) ^ 2 ∂m.tilted

def scoreCDF (m : WeightedModel d) (x : Space d) (y : ℝ) : ℝ≥0∞ :=
  m.joint {θ | inner ℝ θ.1 x + θ.2 ≤ y}

/-- The score-height slice measure `ν_{s,y}` in (3.2). -/
def slopeSlice (m : WeightedModel d) (x u : Space d) (y : ℝ) : Measure ℝ :=
  (m.weights.withDensity (fun w => m.g w (y - inner ℝ w x))).map
    (fun w => inner ℝ w u)

def crossingKernel (m : WeightedModel d) (x u : Space d) (y : ℝ) : ℝ≥0∞ :=
  ∫⁻ a, ∫⁻ a', ENNReal.ofReal (|a - a'|) ∂(m.slopeSlice x u y)
    ∂(m.slopeSlice x u y)

/-- Exact iid visible-crossing contract (3.7), discharged by DistributionFree.exactCrossing. -/
def ExactCrossingClaim : Prop :=
  ∀ (m : WeightedModel d) (K : ℕ), 2 ≤ K → ∀ p : Probe d,
    m.expectedCount K p = (K.choose 2 : ℝ≥0∞) *
      ∫⁻ s in Icc 0 p.length, ∫⁻ y,
        (m.scoreCDF (p.curve s) y) ^ (K - 2) *
          m.crossingKernel (p.curve s) (deriv p.curve s) y

/-- The first main theorem contract (2.6), discharged by DistributionFree.weighted_visibility. -/
def WeightedVisibilityClaim : Prop :=
  ∀ (m : WeightedModel d) (K : ℕ), 2 ≤ K → ∀ p : Probe d,
    m.expectedCount K p ≤ ((K : ℝ≥0∞) * m.average / 2) *
      ∫⁻ s in Icc 0 p.length, m.directionalGini (deriv p.curve s)

/-- The second main inequality contract (2.7), discharged by DistributionFree.weighted_covariance. -/
def WeightedCovarianceClaim : Prop :=
  ∀ (m : WeightedModel d), MemLp (fun w => w) 2 m.tilted →
    ∀ (K : ℕ), 2 ≤ K → ∀ p : Probe d,
      m.expectedCount K p ≤ ((K : ℝ≥0∞) * m.average /
        ENNReal.ofReal (Real.sqrt 3)) *
          ∫⁻ s in Icc 0 p.length,
            ENNReal.ofReal (Real.sqrt (m.projectedVariance (deriv p.curve s)))

/-- The isolated weighted visibility contract (4.1), discharged unconditionally by VisibilityKernel.visibilityLemmaClaim. -/
def VisibilityLemmaClaim : Prop :=
  ∀ (m : WeightedModel d) (n : ℕ) (x u : Space d),
    (∫⁻ y, m.scoreCDF x y ^ n * m.crossingKernel x u y) ≤
      m.average / (n + 1 : ℕ) * m.directionalGini u

end WeightedModel
end Paper35.Source
