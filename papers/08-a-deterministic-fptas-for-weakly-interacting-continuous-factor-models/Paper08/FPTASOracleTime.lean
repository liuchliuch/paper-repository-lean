import Paper08.FPTASCost
import Paper08.EffectiveAccess

/-! # Actual oracle running time through the complete FPTAS

The second component below adds the original oracle's `timeCost` at every
query made by the primitive, moment, uncached recurrence, and support loops.
The first component is proved equal to the existing rational algorithm.
-/
open scoped BigOperators
namespace Paper08.FPTASOracleTime
open PrimitiveMomentsQ FPTASAlgorithm FPTASCost

/-- The previously proved single-query bound, at the actual chosen parameters. -/
def perQueryBound (r s C A degree L : ℕ) (τ : ℚ) : ℕ :=
  let J := Oracle.totalLevelChoice s C τ
  let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
  A * (1 + L + P + r * (2 * J + 3)) ^ degree

section Instrumentation
variable {n m A degree : ℕ}
variable (scopes : Fin m → Finset (Fin n))
variable (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ)
variable (labelBits : Fin m → ℕ)
variable (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))

/-- Restrict the actual timed primitive to the nonzero exponents. -/
def timedSparse (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  EffectiveAccess.timedPrimitive
    (fun i : Fin d.support.card => scopes (d.support.orderEmbOfFin rfl i))
    (fun i => Ψ (d.support.orderEmbOfFin rfl i))
    (fun i => labelBits (d.support.orderEmbOfFin rfl i))
    (fun i => O (d.support.orderEmbOfFin rfl i))
    (fun i => d (d.support.orderEmbOfFin rfl i)) s C τ

/-- The actual multinomial enumeration, charging every primitive call. -/
def timedMoment (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  if j = 0 then (1, 0) else
    (∑ d ∈ Finset.finsuppAntidiag B j,
        (timedSparse scopes Ψ labelBits O d s C τ).1 / factorialWeight d,
      ∑ d ∈ Finset.finsuppAntidiag B j,
        (timedSparse scopes Ψ labelBits O d s C τ).2)

/-- The same uncached recurrence, adding the oracle times of its moment calls. -/
def timedLocal (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  BitComplexity.rationalLogCoeffQueryCost (fun i => timedMoment scopes Ψ labelBits O B i s C τ) j

def timedLog (r c s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  (∑ p ∈ Finset.Icc 1 s, ∑ AB ∈ pairs scopes r c s p,
      (-1 : ℚ) ^ (AB.1.card - AB.2.card) * (timedLocal scopes Ψ labelBits O AB.2 p s C τ).1,
    ∑ p ∈ Finset.Icc 1 s, ∑ AB ∈ pairs scopes r c s p,
      (timedLocal scopes Ψ labelBits O AB.2 p s C τ).2)

/-- The complete program instrumented with actual oracle running time.
Final rational exponentiation makes no additional oracle calls. -/
def timedRun (fixed : Parameters.Fixed) (r c : ℕ) (ε : ℚ) : ℚ × ℕ :=
  if m = 0 then (1, 0) else
    let L := timedLog scopes Ψ labelBits O r c (Parameters.truncationOrder fixed m ε)
      fixed.C (Parameters.primitiveTolerance fixed m ε)
    (Algorithm.rationalExp L.1 ε, L.2)

@[simp] theorem timedSparse_value (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) :
    (timedSparse scopes Ψ labelBits O d s C τ).1 =
      primitiveQ scopes (fun i => (O i).valueOracle.query) d s C τ := by
  exact EffectiveAccess.timedPrimitive_value _ _ _ _ _ _ _ _

@[simp] theorem timedMoment_value (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (timedMoment scopes Ψ labelBits O B j s C τ).1 =
      momentQ scopes (fun i => (O i).valueOracle.query) B j s C τ := by
  by_cases hj : j = 0 <;> simp [timedMoment, momentQ, hj]

@[simp] theorem timedLocal_value (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (timedLocal scopes Ψ labelBits O B j s C τ).1 =
      localCoeff scopes (fun i => (O i).valueOracle.query) B j s C τ := by
  simp only [timedLocal, BitComplexity.rationalLogCoeffQueryCost_value, timedMoment_value, localCoeff]

@[simp] theorem timedLog_value (r c s C : ℕ) (τ : ℚ) :
    (timedLog scopes Ψ labelBits O r c s C τ).1 =
      logApprox scopes (fun i => (O i).valueOracle.query) r c s C τ := by
  simp only [timedLog, logApprox, timedLocal_value]

@[simp] theorem timedRun_value (fixed : Parameters.Fixed) (r c : ℕ) (ε : ℚ) :
    (timedRun scopes Ψ labelBits O fixed r c ε).1 =
      run fixed scopes (fun i => (O i).valueOracle.query) r c ε := by
  simp only [timedRun, run]
  split_ifs <;> simp only [timedLog_value]

variable {r L : ℕ} (hscopes : ∀ i, (scopes i).card ≤ r) (hlabels : ∀ i, labelBits i ≤ L)
include hscopes hlabels

theorem timedSparse_time (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) :
    (timedSparse scopes Ψ labelBits O d s C τ).2 ≤
      primitiveQueries scopes d s C τ * perQueryBound r s C A degree L τ := by
  exact EffectiveAccess.timedPrimitive_time _ (fun i => hscopes _) _ _ _
    (fun i => hlabels _) _ _ _ _

theorem timedMoment_time (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (timedMoment scopes Ψ labelBits O B j s C τ).2 ≤
      momentQueries scopes B j s C τ * perQueryBound r s C A degree L τ := by
  unfold timedMoment momentQueries
  split_ifs
  · simp
  · dsimp only
    calc
      _ ≤ ∑ d ∈ Finset.finsuppAntidiag B j,
          primitiveQueries scopes d s C τ * perQueryBound r s C A degree L τ :=
        Finset.sum_le_sum fun d _ => timedSparse_time scopes Ψ labelBits O hscopes hlabels d s C τ
      _ = _ := (Finset.sum_mul _ _ _).symm

end Instrumentation

/-- Proportional cost transfer through every call of the actual uncached
recurrence. It compares the recursively accumulated costs themselves. -/
theorem recurrence_time_le (M Q : ℕ → ℚ × ℕ) (T j : ℕ)
    (hM : ∀ k, (M k).2 ≤ (Q k).2 * T) :
    (BitComplexity.rationalLogCoeffQueryCost M j).2 ≤
      (BitComplexity.rationalLogCoeffQueryCost Q j).2 * T := by
  induction j using Nat.strongRecOn with
  | ind j ih =>
    by_cases hj : j = 0
    · subst j
      simp [BitComplexity.rationalLogCoeffQueryCost]
    rw [BitComplexity.rationalLogCoeffQueryCost, dif_neg hj,
      BitComplexity.rationalLogCoeffQueryCost, dif_neg hj]
    dsimp only
    rw [Nat.add_mul, Finset.sum_mul]
    apply Nat.add_le_add (hM j)
    apply Finset.sum_le_sum
    intro i _
    rw [Nat.add_mul]
    exact Nat.add_le_add (ih i.val i.isLt) (hM (j - i.val))

section CompleteTime
variable {n m A degree r L : ℕ}
variable (scopes : Fin m → Finset (Fin n))
variable (hscopes : ∀ i, (scopes i).card ≤ r)
variable (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ)
variable (labelBits : Fin m → ℕ)
variable (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
variable (hlabels : ∀ i, labelBits i ≤ L)
include hscopes hlabels

theorem timedLocal_time (B : Finset (Fin m)) (j s C : ℕ) (τ : ℚ) :
    (timedLocal scopes Ψ labelBits O B j s C τ).2 ≤
      (localCoeffWithCost scopes (fun i => (O i).valueOracle.query) B j s C τ).2 *
        perQueryBound r s C A degree L τ := by
  exact recurrence_time_le _ _ _ _
    (fun k => timedMoment_time scopes Ψ labelBits O hscopes hlabels B k s C τ)

theorem timedLog_time (c s C : ℕ) (τ : ℚ) :
    (timedLog scopes Ψ labelBits O r c s C τ).2 ≤
      (logApproxWithCost scopes (fun i => (O i).valueOracle.query) r c s C τ).2 *
        perQueryBound r s C A degree L τ := by
  unfold timedLog logApproxWithCost
  dsimp only
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p _
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum fun AB _ => timedLocal_time scopes hscopes Ψ labelBits O hlabels AB.2 p s C τ

/-- Actual oracle running time is bounded by the actual complete query count
times the single-query polynomial, at the parameters computed by the program. -/
theorem timedRun_time (fixed : Parameters.Fixed) (c : ℕ) (ε : ℚ) :
    (timedRun scopes Ψ labelBits O fixed r c ε).2 ≤
      (runWithCost fixed scopes (fun i => (O i).valueOracle.query) r c ε).2 *
        perQueryBound r (Parameters.truncationOrder fixed m ε) fixed.C A degree L
          (Parameters.primitiveTolerance fixed m ε) := by
  unfold timedRun runWithCost
  split_ifs
  · simp
  · exact timedLog_time scopes hscopes Ψ labelBits O hlabels _ _ _ _

/-- Substitute the proved polynomial query bound into the actual time sum. -/
theorem timedRun_time_queries_polynomial (p : Parameters.Fixed) (c : ℕ) (ε : ℚ)
    (hε : 0 < ε) (hεu : ε ≤ 1) :
    ((timedRun scopes Ψ labelBits O p r c ε).2 : ℚ) ≤
      (4 * (((m + 1 : ℕ) : ℚ) / ε)) ^ queryDegree p r c *
        (perQueryBound r (Parameters.truncationOrder p m ε) p.C A degree L
          (Parameters.primitiveTolerance p m ε) : ℚ) := by
  calc
    _ ≤ (((runWithCost p scopes (fun i => (O i).valueOracle.query) r c ε).2 *
        perQueryBound r (Parameters.truncationOrder p m ε) p.C A degree L
          (Parameters.primitiveTolerance p m ε) : ℕ) : ℚ) := by
      exact_mod_cast timedRun_time scopes hscopes Ψ labelBits O hlabels p c ε
    _ ≤ _ := by
      rw [Nat.cast_mul]
      exact mul_le_mul_of_nonneg_right
        (runWithCost_queries_polynomial p scopes hscopes _ ε hε hεu) (Nat.cast_nonneg _)

end CompleteTime
end Paper08.FPTASOracleTime
