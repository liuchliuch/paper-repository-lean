import Paper08.RationalQuadrature
import Paper08.BitComplexity

/-! # Effective value access and actual oracle time in the primitive loops

This is the running-time part of Assumption 1.1. Bounds apply only to rational
points in the cube and requested precision b≥1, exactly as the value-accuracy
promise does. The time instrumented below is the sum of the actual oracle
running times at the points the program queries; no cost bound is returned as
if it had been measured by the program. Non-oracle rational arithmetic is
accounted for separately.
-/
open scoped BigOperators
namespace Paper08.EffectiveAccess
open CellGrid RationalQuadrature

/-- Original polynomial-time finite-precision access, with fixed uniform
polynomial coefficients and an explicit factor-label encoding length. -/
structure Oracle (dimension : ℕ) (Ψ : (Fin dimension → ℝ) → ℝ)
    (A degree labelBits : ℕ) where
  valueOracle : Paper08.Oracle.Oracle dimension Ψ
  timeCost : (Fin dimension → ℚ) → ℕ → ℕ
  time_bound : ∀ x b, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → 1 ≤ b →
    timeCost x b ≤ A * (1 + labelBits + b + ∑ j, BitComplexity.rationalBits (x j)) ^ degree
  answer_bits_le_time : ∀ x b, (∀ j, 0 ≤ x j ∧ x j ≤ 1) → 1 ≤ b →
    BitComplexity.rationalBits (valueOracle.query x b) ≤ timeCost x b

/-- A unit-interval rational with J fractional dyadic bits needs at most
2J+3 bits in its actual reduced numerator/denominator representation. -/
lemma rationalBits_coordinate {J : ℕ} {q : ℚ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hdy : Paper08.Oracle.IsDyadicAt J q) : BitComplexity.rationalBits q ≤ 2 * J + 3 := by
  have hd : q.den ≤ 2 ^ J := Nat.le_of_dvd (by positivity) hdy.den_dvd
  have hn := Moments.rational_num_size_le_of_abs_den_le q 0 J
    (by simpa only [pow_zero, abs_of_nonneg hq0] using hq1) hd
  have hds : q.den.size ≤ J + 1 := by
    apply Nat.size_le.mpr
    rw [pow_succ]
    have hp : 0 < (2 : ℕ) ^ J := by positivity
    omega
  unfold BitComplexity.rationalBits
  omega

/-- The actual retained-cell query points satisfy the reduced-encoding bound. -/
lemma local_coordinate_bits {n t J : ℕ} (scopes : Fin t → Finset (Fin n))
    {ν : Fin t → ℕ} (hν : ν ∈ TupleCount.boundedTuples t J)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) {l : ℕ} (hl : l ≤ ν i)
    (j : Fin (scopes i).card) :
    BitComplexity.rationalBits (queryPoint l (localIndex scopes ν z i l) j) ≤ 2 * J + 3 := by
  have hv := local_query_valid scopes hν z i hl j
  exact rationalBits_coordinate hv.1 hv.2.1 hv.2.2

lemma local_query_bits {n t r J : ℕ} (scopes : Fin t → Finset (Fin n))
    (hscopes : ∀ i, (scopes i).card ≤ r)
    {ν : Fin t → ℕ} (hν : ν ∈ TupleCount.boundedTuples t J)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) {l : ℕ} (hl : l ≤ ν i) :
    (∑ j, BitComplexity.rationalBits (queryPoint l (localIndex scopes ν z i l) j)) ≤ r * (2 * J + 3) := by
  calc
    _ ≤ ∑ _j : Fin (scopes i).card, (2 * J + 3) :=
      Finset.sum_le_sum fun j _ => local_coordinate_bits scopes hν z i hl j
    _ = (scopes i).card * (2 * J + 3) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (hscopes i)

/-- Single-query polynomial time, derived for the actual points, not promised
as a special-purpose primitive-loop certificate. -/
theorem local_query_time {n t r J P A degree L : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (hP : 1 ≤ P)
    {ν : Fin t → ℕ} (hν : ν ∈ TupleCount.boundedTuples t J)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) {l : ℕ} (hl : l ≤ ν i) :
    (O i).timeCost (queryPoint l (localIndex scopes ν z i l)) P ≤
      A * (1 + L + P + r * (2 * J + 3)) ^ degree := by
  have hv := local_query_valid scopes hν z i hl
  have hp := (O i).time_bound _ P (fun j => ⟨(hv j).1, (hv j).2.1⟩) hP
  apply hp.trans
  apply Nat.mul_le_mul_left A
  apply Nat.pow_le_pow_left
  have hbits := local_query_bits scopes hscopes hν z i hl
  have hlabel := hlabels i
  omega

/-- The original promise also bounds the actual returned oracle answer's encoding. -/
theorem local_answer_bits {n t r J P A degree L : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (hP : 1 ≤ P)
    {ν : Fin t → ℕ} (hν : ν ∈ TupleCount.boundedTuples t J)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) {l : ℕ} (hl : l ≤ ν i) :
    BitComplexity.rationalBits ((O i).valueOracle.query
      (queryPoint l (localIndex scopes ν z i l)) P) ≤
      A * (1 + L + P + r * (2 * J + 3)) ^ degree := by
  have hv := local_query_valid scopes hν z i hl
  exact ((O i).answer_bits_le_time _ P (fun j => ⟨(hv j).1, (hv j).2.1⟩) hP).trans
    (local_query_time scopes hscopes Ψ labelBits O hlabels hP hν z i hl)

/-- A sampled primitive factor paired with its actual oracle running time.
The rational log/power/rounding operations are deliberately not charged here. -/
def timedStep {n t A degree : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (α : Fin t → ℕ) (P : ℕ) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ) : ℚ × ℕ :=
  let x := queryPoint l (localIndex scopes ν z i l)
  (Paper08.Oracle.primitiveSampleQ P (α i) ((O i).valueOracle.query x P), (O i).timeCost x P)

/-- Execute exactly the one or two actual oracle calls used by an increment. -/
def timedIncrement {n t A degree : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (α : Fin t → ℕ) (P : ℕ) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) : ℚ × ℕ :=
  match ν i with
  | 0 => timedStep scopes Ψ labelBits O α P ν z i 0
  | l + 1 =>
      let fine := timedStep scopes Ψ labelBits O α P ν z i (l + 1)
      let coarse := timedStep scopes Ψ labelBits O α P ν z i l
      (fine.1 - coarse.1, fine.2 + coarse.2)

/-- The original nested level/cell/factor loops with their actual timeCost sums. -/
def timedRule {n t A degree : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (α : Fin t → ℕ) (J P : ℕ) : ℚ × ℕ :=
  (∑ ν ∈ TupleCount.boundedTuples t J,
    ∑ z : Grid (commonLevels scopes ν), weightQ (commonLevels scopes ν) *
      ∏ i, (timedIncrement scopes Ψ labelBits O α P ν z i).1,
   ∑ ν ∈ TupleCount.boundedTuples t J,
    ∑ z : Grid (commonLevels scopes ν), ∑ i, (timedIncrement scopes Ψ labelBits O α P ν z i).2)

/-- The actual generic primitive parameter choices, with oracle time instrumentation. -/
def timedPrimitive {n t A degree : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (α : Fin t → ℕ) (s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  let J := Paper08.Oracle.totalLevelChoice s C τ
  let P := Paper08.Oracle.samplePrecision s (Paper08.Oracle.primitiveSampleTol s J C τ)
  timedRule scopes Ψ labelBits O α J P

lemma timedIncrement_value {n t A degree : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (α : Fin t → ℕ) (P : ℕ) (ν : Fin t → ℕ)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (timedIncrement scopes Ψ labelBits O α P ν z i).1 = incrementQ scopes
      (primitiveTable scopes (fun i => (O i).valueOracle.query) α P) ν z i := by
  unfold timedIncrement incrementQ
  generalize he : ν i = l
  cases l <;> rfl

@[simp] theorem timedRule_value {n t A degree : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (α : Fin t → ℕ) (J P : ℕ) :
    (timedRule scopes Ψ labelBits O α J P).1 =
      ruleQ scopes (primitiveTable scopes (fun i => (O i).valueOracle.query) α P) J := by
  simp only [timedRule, ruleQ, timedIncrement_value]

@[simp] theorem timedPrimitive_value {n t A degree : ℕ} (scopes : Fin t → Finset (Fin n))
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (α : Fin t → ℕ) (s C : ℕ) (τ : ℚ) :
    (timedPrimitive scopes Ψ labelBits O α s C τ).1 =
      primitiveRuleQ scopes (fun i => (O i).valueOracle.query) α s C τ := by
  simp only [timedPrimitive, primitiveRuleQ, timedRule_value]

/-- Bound an increment by the actual number of calls it executes. -/
lemma timedIncrement_time {n t r J P A degree L : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (hP : 1 ≤ P) (α : Fin t → ℕ)
    {ν : Fin t → ℕ} (hν : ν ∈ TupleCount.boundedTuples t J)
    (z : Grid (commonLevels scopes ν)) (i : Fin t) :
    (timedIncrement scopes Ψ labelBits O α P ν z i).2 ≤
      (if ν i = 0 then 1 else 2) * (A * (1 + L + P + r * (2 * J + 3)) ^ degree) := by
  have hstep : ∀ l, l ≤ ν i → (timedStep scopes Ψ labelBits O α P ν z i l).2 ≤
      A * (1 + L + P + r * (2 * J + 3)) ^ degree := by
    intro l hl
    exact local_query_time scopes hscopes Ψ labelBits O hlabels hP hν z i hl
  unfold timedIncrement
  generalize he : ν i = l
  cases l with
  | zero => simpa using hstep 0 (by omega)
  | succ l =>
      have hf := hstep (l + 1) (by omega)
      have hc := hstep l (by omega)
      simp only [Nat.succ_ne_zero, if_false]
      omega

/-- The actual accumulated oracle time is at most actual query count times
the proved single-query polynomial bound. -/
theorem timedRule_time {n t r J P A degree L : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (hP : 1 ≤ P) (α : Fin t → ℕ) :
    (timedRule scopes Ψ labelBits O α J P).2 ≤
      queryCalls scopes J * (A * (1 + L + P + r * (2 * J + 3)) ^ degree) := by
  unfold timedRule
  dsimp only
  calc
    _ ≤ ∑ ν ∈ TupleCount.boundedTuples t J,
        ∑ _z : Grid (commonLevels scopes ν), ∑ i : Fin t,
          (if ν i = 0 then 1 else 2) * (A * (1 + L + P + r * (2 * J + 3)) ^ degree) := by
      apply Finset.sum_le_sum
      intro ν hν
      apply Finset.sum_le_sum
      intro z _
      exact Finset.sum_le_sum fun i _ => timedIncrement_time scopes hscopes Ψ labelBits O hlabels hP α hν z i
    _ = _ := by simp_rw [← Finset.sum_mul]; rfl

/-- Oracle running time for the primitive routine at its actual chosen J and P. -/
theorem timedPrimitive_time {n t r A degree L : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (α : Fin t → ℕ) (s C : ℕ) (τ : ℚ) :
    let J := Paper08.Oracle.totalLevelChoice s C τ
    let P := Paper08.Oracle.samplePrecision s (Paper08.Oracle.primitiveSampleTol s J C τ)
    (timedPrimitive scopes Ψ labelBits O α s C τ).2 ≤
      queryCalls scopes J * (A * (1 + L + P + r * (2 * J + 3)) ^ degree) := by
  dsimp only [timedPrimitive]
  exact timedRule_time scopes hscopes Ψ labelBits O hlabels (Paper08.Oracle.samplePrecision_pos _ _) α

end Paper08.EffectiveAccess
