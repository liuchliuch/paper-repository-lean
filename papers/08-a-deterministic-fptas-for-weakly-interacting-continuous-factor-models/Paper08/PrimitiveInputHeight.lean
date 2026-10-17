import Paper08.PrimitiveIntegralProgram

/-! # Heights of the actual primitive and moment input leaves

Only oracle answers at the retained dyadic cells occur in these expressions.
Their encoding bounds below follow from the original effective-access promise;
the final expression-height theorems take no separate answer-size certificate.
-/
open scoped BigOperators
namespace Paper08.PrimitiveInputHeight
open RationalProgram PrimitiveProgram PrimitiveExpressions PrimitiveIntegralProgram
open CellGrid RationalQuadrature PrimitiveMomentsQ

lemma height_le_rationalBits (q : ℚ) : height q ≤ BitComplexity.rationalBits q := by
  unfold height BitComplexity.rationalBits
  omega

lemma weightExpr_inputHeight {n : ℕ} (m : Fin n → ℕ) :
    (weightExpr m).inputHeight ≤ 2 := by
  apply max_le
  · norm_num [Expr.inputHeight, height]
  · exact twoPower_inputHeight _

theorem ruleExpr_inputHeight {n t P J H : ℕ}
    (scopes : Fin t → Finset (Fin n)) (query : LocalQueries scopes) (α : Fin t → ℕ)
    (hH : 2 * P + 6 ≤ H)
    (hanswers : ∀ ν ∈ TupleCount.boundedTuples t J,
      ∀ (z : Grid (commonLevels scopes ν)) (i : Fin t) (l : ℕ), l ≤ ν i →
      height (query i (queryPoint l (localIndex scopes ν z i l)) P) ≤ H) :
    (ruleExpr scopes query α P J).inputHeight ≤ H := by
  letI := tupleOrder t
  unfold ruleExpr
  apply sumSet_inputHeight _ _ (by omega)
  intro ν hν
  letI := gridOrder (commonLevels scopes ν)
  apply sumSet_inputHeight _ _ (by omega)
  intro z _
  apply max_le
  · exact (weightExpr_inputHeight _).trans (by omega)
  · apply productSet_inputHeight _ _ (by omega)
    intro i _
    have hstep : ∀ l, l ≤ ν i → (stepExpr scopes query α P ν z i l).inputHeight ≤ H := by
      intro l hl
      exact primitiveSampleExpr_inputHeight P (α i) _ hH (hanswers ν hν z i l hl)
    unfold incrementExpr
    split
    · exact hstep 0 (by omega)
    · rename_i l hl
      exact max_le (hstep (l + 1) (by omega)) (hstep l (by omega))

/-- A uniform input-height bound, including the actual oracle answer leaves. -/
def inputBound (A degree L r J P s : ℕ) : ℕ :=
  A * (1 + L + P + r * (2 * J + 3)) ^ degree + 2 * P + s + 8

theorem ruleExpr_inputHeight_effective {n t r J P A degree L s : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (hP : 1 ≤ P) (α : Fin t → ℕ) :
    (ruleExpr scopes (fun i => (O i).valueOracle.query) α P J).inputHeight ≤
      inputBound A degree L r J P s := by
  apply ruleExpr_inputHeight scopes _ α (by unfold inputBound; omega)
  intro ν hν z i l hl
  have hb := EffectiveAccess.local_answer_bits scopes hscopes Ψ labelBits O hlabels hP hν z i hl
  exact ((height_le_rationalBits _).trans hb).trans (by unfold inputBound; omega)

/-- Parameters here are exactly those used by `primitiveRuleQ`. -/
theorem primitiveExpr_inputHeight_effective {n t r A degree L s C : ℕ}
    (scopes : Fin t → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin t) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin t → ℕ)
    (O : (i : Fin t) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (α : Fin t → ℕ) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (primitiveExpr scopes (fun i => (O i).valueOracle.query) α s C τ).inputHeight ≤
      inputBound A degree L r J P s := by
  exact ruleExpr_inputHeight_effective scopes hscopes Ψ labelBits O hlabels
    (Oracle.samplePrecision_pos _ _) α

theorem sparseExpr_inputHeight_effective {n m r A degree L s C : ℕ}
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (d : Fin m →₀ ℕ) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (sparseExpr scopes (fun i => (O i).valueOracle.query) d s C τ).inputHeight ≤
      inputBound A degree L r J P s := by
  exact primitiveExpr_inputHeight_effective _ (fun i => hscopes _)
    (fun i => Ψ (d.support.orderEmbOfFin rfl i))
    (fun i => labelBits (d.support.orderEmbOfFin rfl i))
    (fun i => O (d.support.orderEmbOfFin rfl i))
    (fun i => hlabels _) _ τ

lemma factorialWeightExpr_inputHeight {m s : ℕ} (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) :
    (factorialWeightExpr d).inputHeight ≤ s + 2 := by
  apply productSet_inputHeight _ _ (by omega)
  intro e he
  have hde : d e ≤ s := by
    have hh := Finset.single_le_sum (fun i _ => Nat.zero_le (d i)) he
    change (∑ i ∈ d.support, d i) ≤ s at hd
    omega
  exact (RationalRecurrenceProgram.inputHeight_factorial_le _).trans (by omega)

/-- This theorem uses only the original oracle time/encoding promise and the
moment order bound. Every raw answer in the actual retained-cell expression
is bounded by `local_answer_bits`; no per-answer bound is assumed. -/
theorem momentExpr_inputHeight_effective {n m r A degree L j s C : ℕ}
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (B : Finset (Fin m)) (hj : j ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    (momentExpr scopes (fun i => (O i).valueOracle.query) B j s C τ).inputHeight ≤
      inputBound A degree L r J P s := by
  dsimp only
  by_cases hj0 : j = 0
  · simp only [momentExpr, if_pos hj0, Expr.inputHeight]
    rw [show height (1 : ℚ) = 1 by simp [height]]
    unfold inputBound
    omega
  · letI := exponentOrder m
    unfold momentExpr
    rw [if_neg hj0]
    apply sumSet_inputHeight _ _ (by unfold inputBound; omega)
    intro d hd
    apply max_le
    · exact sparseExpr_inputHeight_effective scopes hscopes Ψ labelBits O hlabels d τ
    · have hdeg : d.degree ≤ s := by
        have hh := (Finset.mem_finsuppAntidiag'.mp hd).1
        change (∑ e ∈ d.support, d e) ≤ s
        change (∑ e ∈ d.support, d e) = j at hh
        omega
      exact (factorialWeightExpr_inputHeight d hdeg).trans (by unfold inputBound; omega)

end Paper08.PrimitiveInputHeight
