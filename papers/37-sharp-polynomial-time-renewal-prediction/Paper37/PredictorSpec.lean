import Paper37.RenewalLikelihood
import Paper37.Boundary
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.List.ToFinsupp
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
Exact source-level objects on binary words. The exhaustive sums specify the
assignment; no complexity guarantee is attached to these definitions. A proof
that the multiset DP computes these sums remains an explicit coverage obligation.
-/
noncomputable section
namespace Paper37.Prediction
open scoped BigOperators ENNReal
open Paper37.Renewal MeasureTheory

/-- The completed-gap envelope in rational arithmetic, equation (B.2). -/
def gapEnvelope (gaps : List ℕ) : ℚ :=
  ∏ d ∈ gaps.toFinset, ((gaps.count d : ℚ) / (gaps.length : ℚ)) ^ gaps.count d

def wordEnvelope (x : List Bool) : ℚ := gapEnvelope (gapsFrom 0 x)

lemma gapEnvelope_pos (g : List ℕ) : 0 < gapEnvelope g := by
  by_cases hg : g = []
  · simp [gapEnvelope, hg]
  have hl : 0 < g.length := by cases g <;> simp_all
  have hlr : (0 : ℚ) < g.length := by exact_mod_cast hl
  apply Finset.prod_pos
  intro d hd
  by_cases hc : g.count d = 0
  · simp [hc]
  · exact pow_pos (div_pos (by exact_mod_cast Nat.pos_of_ne_zero hc) hlr) _

lemma wordEnvelope_pos (x : List Bool) : 0 < wordEnvelope x := gapEnvelope_pos _

def ordinaryNormalizer (L : ℕ) : ℚ :=
  ∑ x ∈ (words L).toFinset, wordEnvelope x

lemma ordinaryNormalizer_pos (L : ℕ) : 0 < ordinaryNormalizer L := by
  apply Finset.sum_pos'
  · intro x hx; exact (wordEnvelope_pos x).le
  · refine ⟨List.replicate L false, ?_, wordEnvelope_pos _⟩
    simpa using (mem_words L (List.replicate L false)).mpr (by simp)

def ordinaryAssignment (x : List Bool) : ℚ :=
  wordEnvelope x / ordinaryNormalizer x.length

lemma ordinaryAssignment_pos (x : List Bool) : 0 < ordinaryAssignment x :=
  div_pos (wordEnvelope_pos x) (ordinaryNormalizer_pos x.length)

/-- The suffix after the first observed renewal. -/
def firstSuffix : List Bool → Option (List Bool)
  | [] => none
  | false::x => firstSuffix x
  | true::x => some x

/-- The uniform first-renewal mixture B.7 on the source binary alphabet. -/
def blockAssignment (x : List Bool) : ℚ :=
  (match firstSuffix x with
    | none => 1
    | some suffix => ordinaryAssignment suffix) / (x.length+1 : ℚ)

lemma blockAssignment_pos (x : List Bool) : 0 < blockAssignment x := by
  apply div_pos
  · split <;> simp_all [ordinaryAssignment_pos]
  · positivity

/-- Exact unnormalized continuation mass (C.1). -/
def continuationMass (L : ℕ) (z : List Bool) : ℚ :=
  ∑ v ∈ (words (L-z.length)).toFinset, wordEnvelope (z ++ v)

/-- Prefix probability under the horizon-specific B.7 assignment. -/
def prefixMass (N : ℕ) (z : List Bool) : ℚ :=
  ∑ v ∈ (words (N-z.length)).toFinset, blockAssignment (z ++ v)

def blockConditional (N : ℕ) (z : List Bool) : ℚ :=
  prefixMass N (z ++ [true]) / prefixMass N z

/-- The exact deterministic predictor D.1. Input histories are length n. -/
def predict (n : ℕ) (x : List Bool) : ℚ :=
  (∑ t ∈ Finset.Icc 1 n, blockConditional (n+1) (x.drop (n-t))) / n

/-- General privately randomized predictors, with no computational restriction.
The probability measure for an observed history is supported on [0,1]. -/
abbrev RandomizedPredictor := List Bool → ProbabilityMeasure (Set.Icc (0 : ℝ) 1)

/-- Genuine stationary conditional KL risk, including infinite endpoint losses. -/
def risk (n : ℕ) (q : RandomizedPredictor) (μ : Law) : ℝ≥0∞ :=
  ∑ x ∈ (words n).toFinset, ENNReal.ofReal (blockMass μ x) *
    ∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl (conditional μ x) r.val ∂(q x).toMeasure

/-- The source ordinary-hazard substitution, deliberately different on zeros. -/
def substitutedTarget (μ : Law) (x : List Bool) : ℝ :=
  μ.mass (ageFrom 0 x) / tail μ (ageFrom 0 x)

def substitutedRisk (n : ℕ) (q : RandomizedPredictor) (μ : Law) : ℝ≥0∞ :=
  ∑ x ∈ (words n).toFinset, ENNReal.ofReal (blockMass μ x) *
    ∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl (substitutedTarget μ x) r.val ∂(q x).toMeasure

def minimaxRisk (n : ℕ) : ℝ≥0∞ := ⨅ q : RandomizedPredictor, ⨆ μ : Law, risk n q μ

def substitutedMinimaxRisk (n : ℕ) : ℝ≥0∞ :=
  ⨅ q : RandomizedPredictor, ⨆ μ : Law, substitutedRisk n q μ

/-- The history-wise criterion from Proposition A.2. Null histories are excluded. -/
def historywiseRisk (n : ℕ) (q : RandomizedPredictor) (μ : Law) : ℝ≥0∞ :=
  ⨆ x : {x : List Bool // x.length = n ∧ 0 < blockMass μ x},
    ∫⁻ r : Set.Icc (0 : ℝ) 1, Boundary.kl (conditional μ x.val) r.val ∂(q x.val).toMeasure

def historywiseMinimaxRisk (n : ℕ) : ℝ≥0∞ :=
  ⨅ q : RandomizedPredictor, ⨆ μ : Law, historywiseRisk n q μ

end Paper37.Prediction
