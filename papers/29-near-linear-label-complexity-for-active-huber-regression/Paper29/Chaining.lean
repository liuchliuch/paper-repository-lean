import Paper29.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-! Literal partition definition of Talagrand's γ₂ used in equation (3.7).
Distances take nonnegative extended-real values so the infimum is meaningful
also for an unbounded metric. No covering bound is assumed by this definition. -/
noncomputable section
open scoped ENNReal

namespace Paper29.Chaining

structure AdmissiblePartitions (T : Type*) where
  cell : ℕ → Setoid T
  initial : ∀ x y, (cell 0).r x y
  nested : ∀ k x y, (cell (k + 1)).r x y → (cell k).r x y
  finite : ∀ k, Finite (Quotient (cell k))
  cardinality : ∀ k, Nat.card (Quotient (cell k)) ≤ 2 ^ (2 ^ k)

def cellDiameter {T : Type*} (d : T → T → ℝ≥0∞)
    (P : AdmissiblePartitions T) (k : ℕ) (t : T) : ℝ≥0∞ :=
  ⨆ (x : T) (_ : (P.cell k).r t x) (y : T) (_ : (P.cell k).r t y), d x y

def gamma2 {T : Type*} (d : T → T → ℝ≥0∞) : ℝ≥0∞ :=
  ⨅ P : AdmissiblePartitions T, ⨆ t : T,
    ∑' k : ℕ, ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) * cellDiameter d P k t

def huberMetric {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ : Fin n → ℝ) (h k : Fin d → ℝ) : ℝ≥0∞ :=
  ⨆ i : Fin n, ENNReal.ofReal (Real.sqrt (huber ((A.mulVec (h - k)) i) / τ i))

def ball {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (R : ℝ) : Set (Fin d → ℝ) :=
  {h | unshifted A h ≤ R}

/-- The unproved all-radius score statement, Lemma 3.4. -/
def AllRadiusScoresStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (N r : ℕ) (A : Matrix (Fin N) (Fin r) ℝ),
    A.rank = r → (∀ i, ∃ j, A i j ≠ 0) →
    ∃ τ : Fin N → ℝ, (∀ i, 0 < τ i) ∧
      (∑ i, τ i) ≤ C * r * Real.log (2 * N) ∧
      ∀ R : ℝ, 0 < R →
        gamma2 (T := ball A R) (fun h k => huberMetric A τ h k) ≤
          ENNReal.ofReal (C * Real.sqrt R * Real.log (2 * N) ^ (3 / 2 : ℝ))

end Paper29.Chaining
