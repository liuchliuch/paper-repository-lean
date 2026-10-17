import Paper29.Defs
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

/-!
A label-query model for the main results. A policy is an arbitrary mathematical
function of a private seed and the observed finite history. The `diverge` case
includes any internal computation that never requests a new label or returns.
The freshness predicate is the cache normalization described in Section 2.
No correctness or complexity conclusion is built into a policy.
-/
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace Paper29.QueryModel

abbrev History (n : ℕ) := List (Fin n × ℝ)

inductive Decision (n d : ℕ) where
  | output (x : Fin d → ℝ)
  | query (i : Fin n)
  | diverge

def Decision.encode {n d : ℕ} : Decision n d → (Fin d → ℝ) ⊕ (Fin n ⊕ Unit)
  | .output x => .inl x
  | .query i => .inr (.inl i)
  | .diverge => .inr (.inr ())

instance {n d : ℕ} : MeasurableSpace (Decision n d) :=
  MeasurableSpace.comap Decision.encode inferInstance

abbrev Policy (Ω : Type*) (n d : ℕ) := Ω → History n → Decision n d

def Fresh {Ω : Type*} {n d : ℕ} (p : Policy Ω n d) : Prop :=
  ∀ ω h i, p ω h = Decision.query i → i ∉ h.map Prod.fst

def execute {Ω : Type*} {n d : ℕ} (p : Policy Ω n d) (ω : Ω)
    (b : Fin n → ℝ) : ℕ → History n → Option ((Fin d → ℝ) × History n)
  | 0, _ => none
  | k + 1, h => match p ω h with
    | .output x => some (x, h)
    | .query i => execute p ω b k (h ++ [(i, b i)])
    | .diverge => none

def run {Ω : Type*} {n d : ℕ} (p : Policy Ω n d) (ω : Ω) (b : Fin n → ℝ) :=
  execute p ω b (n + 1) []

def queryCount {Ω : Type*} {n d : ℕ} (p : Policy Ω n d) (ω : Ω)
    (b : Fin n → ℝ) : ℝ≥0∞ :=
  match run p ω b with
  | none => ⊤
  | some (_, h) => (h.map Prod.fst).toFinset.card

def Successful {Ω : Type*} {n d : ℕ} (p : Policy Ω n d)
    (A : Matrix (Fin n) (Fin d) ℝ) (b : Fin n → ℝ) (ε : ℝ) (ω : Ω) : Prop :=
  ∃ x h, run p ω b = some (x, h) ∧
    ∀ y, Real.sqrt (objective A b x) ≤ (1 + ε) * Real.sqrt (objective A b y)

def Correct {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ} (μ : Measure Ω)
    (p : Policy Ω n d) (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ) : Prop :=
  Fresh p ∧ (∀ h, Measurable (fun ω => p ω h)) ∧ ∀ b, MeasurableSet {ω | Successful p A b ε ω} ∧
    Measurable (fun ω => queryCount p ω b) ∧
    (99 / 100 : ℝ≥0∞) ≤ μ {ω | Successful p A b ε ω}

/-- A nonadaptive procedure selects its finite queried set before seeing labels.
The output can depend on precisely the labels in that set. -/
structure NonadaptiveProcedure (Ω : Type*) (n d : ℕ) where
  queried : Ω → Finset (Fin n)
  output : (ω : Ω) → ({i // i ∈ queried ω} → ℝ) → (Fin d → ℝ)

def NonadaptiveProcedure.answer {Ω : Type*} {n d : ℕ}
    (p : NonadaptiveProcedure Ω n d) (ω : Ω) (b : Fin n → ℝ) : Fin d → ℝ :=
  p.output ω (fun i => b i)

def NonadaptiveCorrect {Ω : Type*} [MeasurableSpace Ω] {n d : ℕ}
    (μ : Measure Ω) (p : NonadaptiveProcedure Ω n d)
    (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ) : Prop :=
  (∀ i, MeasurableSet {ω | i ∈ p.queried ω}) ∧
  (∀ b, Measurable (fun ω => p.answer ω b)) ∧
  ∀ b, MeasurableSet {ω | ∀ y, Real.sqrt (objective A b (p.answer ω b)) ≤
      (1 + ε) * Real.sqrt (objective A b y)} ∧
    (99 / 100 : ℝ≥0∞) ≤ μ {ω | ∀ y,
      Real.sqrt (objective A b (p.answer ω b)) ≤
        (1 + ε) * Real.sqrt (objective A b y)}

def upperBudget (n r : ℕ) (C ε : ℝ) : ℝ :=
  min (n : ℝ) (C * r * (Real.log (2 * n) ^ 6 + Real.log (2 * n) ^ 4 / ε ^ 2))

def lowerBudget (n r : ℕ) (c ε : ℝ) : ℝ := min (n : ℝ) (r / ε ^ 2) * c

/-- Exact quantifiers of Theorem 2.1; a proposition, not a proved theorem. -/
def UpperBoundStatement : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ (n d : ℕ) (A : Matrix (Fin n) (Fin d) ℝ) (ε : ℝ),
    0 < ε → ε < 1 / 2 →
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
      @IsProbabilityMeasure Ω mΩ μ ∧
      ∃ p : NonadaptiveProcedure Ω n d,
        @NonadaptiveCorrect Ω mΩ n d μ p A ε ∧
        ∀ ω, ((p.queried ω).card : ℝ) ≤ upperBudget n A.rank C ε

/-- Exact fixed-design adaptive lower-bound quantifiers of Theorem 2.2.
Expected counts are extended nonnegative reals, so nontermination costs ∞. -/
def LowerBoundStatement : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ (n d r : ℕ),
    1 ≤ r → r ≤ min n d → ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 800 →
    ∃ A : Matrix (Fin n) (Fin d) ℝ, A.rank = r ∧
      ∀ (Ω : Type) (mΩ : MeasurableSpace Ω) (μ : @Measure Ω mΩ),
        @IsProbabilityMeasure Ω mΩ μ → ∀ p : Policy Ω n d,
        @Correct Ω mΩ n d μ p A ε →
        ENNReal.ofReal (lowerBudget n r c ε) ≤
          ⨆ b : Fin n → ℝ, @lintegral Ω mΩ μ (fun ω => queryCount p ω b)

end Paper29.QueryModel
