import Paper08.PrimitiveInputHeight
import Paper08.PrimitiveParameters
import Paper08.SchoolbookArithmetic
import Paper08.FPTASOracleTime

/-! # The effective primitive integration algorithm of Lemma 3.3

This module assembles the actual rational sparse quadrature, its error relative
to the ambient integral, its computed parameters and query domain, and the bit
cost of executing every arithmetic operation with the schoolbook kernels.
Oracle answer sizes follow from the original effective-access hypothesis.
-/
open scoped BigOperators
namespace Paper08.PrimitiveAlgorithm
open RationalProgram PrimitiveIntegralProgram PrimitiveMomentsQ CellGrid RationalQuadrature

/-- The concrete arithmetic executor, with all logarithm, power, projection,
rounding, cell, and level operations present in the sparse expression. -/
def execute {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (query : Queries scopes)
    (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) : ℚ × ℕ :=
  SchoolbookArithmetic.execute (sparseExpr scopes query d s C τ)

@[simp] theorem execute_value {n m : ℕ} (scopes : Fin m → Finset (Fin n))
    (query : Queries scopes) (d : Fin m →₀ ℕ) (s C : ℕ) (τ : ℚ) :
    (execute scopes query d s C τ).1 = primitiveQ scopes query d s C τ :=
  (SchoolbookArithmetic.execute_spec _).1.trans (sparseExpr_eval _ _ _ _ _ _)

/-- The genuine active-factor enumeration used by sparse quadrature. -/
abbrev activeScopes {n m : ℕ} (scopes : Fin m → Finset (Fin n)) (d : Fin m →₀ ℕ) :=
  fun i : Fin d.support.card => scopes (d.support.orderEmbOfFin rfl i)

/-- Implemented arithmetic bit cost from the actual expression and the
original oracle's answer encoding bound, without an output/cost certificate. -/
theorem execute_bitCost {n m r A degree L s C : ℕ}
    (scopes : Fin m → Finset (Fin n)) (hscopes : ∀ i, (scopes i).card ≤ r)
    (Ψ : (i : Fin m) → (Fin (scopes i).card → ℝ) → ℝ) (labelBits : Fin m → ℕ)
    (O : (i : Fin m) → EffectiveAccess.Oracle (scopes i).card (Ψ i) A degree (labelBits i))
    (hlabels : ∀ i, labelBits i ≤ L) (d : Fin m →₀ ℕ) (hd : d.degree ≤ s) (τ : ℚ) :
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    let N := primitiveNodes r s P J
    let H := PrimitiveInputHeight.inputBound A degree L r J P s
    (execute scopes (fun i => (O i).valueOracle.query) d s C τ).2 ≤
      10000 * N * (4 * ((H + 2) * (N + 1)) + 3) ^ 3 := by
  dsimp only
  have hn := sparseExpr_operations (C := C) scopes hscopes
    (fun i => (O i).valueOracle.query) d hd τ
  have hh := PrimitiveInputHeight.sparseExpr_inputHeight_effective (s := s) (C := C)
    scopes hscopes Ψ labelBits O hlabels d τ
  apply (SchoolbookArithmetic.execute_cost_polynomial _).trans
  gcongr

/-- **Lemma 3.3, actual program and bit complexity.**

For a sparse exponent vector of degree between one and s, execution returns
the computed rational primitive, approximates the original cube integral
within τ, uses the actual linear-size parameters J and P, and queries only
valid J-dyadic cube points at precision P≥1. Its expression-node bound N is
`2^((r+1)J+s)` times the explicit polynomial in `primitiveNodes`; H is the
uniform polynomial oracle-answer bound plus the small arithmetic constants.
The last clause charges the actual oracle `timeCost` separately.
-/
theorem lemma33 {n r m A degree L s C : ℕ} (E : FactorFamily n r m)
    (labelBits : Fin m → ℕ)
    (O : (e : Fin m) → EffectiveAccess.Oracle (E e).scope.card (E e).psi.toFun
      A degree (labelBits e))
    (hlabels : ∀ e, labelBits e ≤ L)
    (d : Fin m →₀ ℕ) (hd0 : 1 ≤ d.degree) (hd : d.degree ≤ s)
    {q K : ℝ} (hq : 0 ≤ q) (hqthird : q < 1 / 3) (hK : 0 ≤ K)
    (hE : ∀ e, (E e).RangeOk q) (hLip : ∀ e, (E e).LipOk K)
    (hC : 2 ≤ C) (hqC : 2 * q ≤ (C : ℝ)) (hKC : 6 * Real.sqrt r * K ≤ (C : ℝ))
    (τ : ℚ) (hτ : 0 < τ) :
    let scopes := fun e => (E e).scope
    let query := fun e => (O e).valueOracle.query
    let J := Oracle.totalLevelChoice s C τ
    let P := Oracle.samplePrecision s (Oracle.primitiveSampleTol s J C τ)
    let N := primitiveNodes r s P J
    let H := PrimitiveInputHeight.inputBound A degree L r J P s
    (execute scopes query d s C τ).1 = primitiveQ scopes query d s C τ ∧
    |((execute scopes query d s C τ).1 : ℝ) - primitive E d| ≤ (τ : ℝ) ∧
    J ≤ (2 * PrimitiveParameters.baseLog C + 4) *
      (s + PrimitiveParameters.toleranceLog τ) ∧
    P ≤ (3 * PrimitiveParameters.baseLog C + 14) *
      (s + PrimitiveParameters.toleranceLog τ) ∧
    1 ≤ P ∧
    FPTASCost.primitiveQueries scopes d s C τ ≤
      2 * s * 2 ^ ((r + 1) * J + s) ∧
    (∀ (ν : Fin d.support.card → ℕ), ν ∈ TupleCount.boundedTuples d.support.card J →
      ∀ (z : Grid (commonLevels (activeScopes scopes d) ν)) (i : Fin d.support.card)
        (l : ℕ), l ≤ ν i → ∀ j,
        0 ≤ queryPoint l (localIndex (activeScopes scopes d) ν z i l) j ∧
        queryPoint l (localIndex (activeScopes scopes d) ν z i l) j ≤ 1 ∧
        Oracle.IsDyadicAt J (queryPoint l (localIndex (activeScopes scopes d) ν z i l) j)) ∧
    (sparseExpr scopes query d s C τ).operations ≤ N ∧
    (sparseExpr scopes query d s C τ).inputHeight ≤ H ∧
    (execute scopes query d s C τ).2 ≤ 10000 * N * (4 * ((H + 2) * (N + 1)) + 3) ^ 3 ∧
    (FPTASOracleTime.timedSparse scopes (fun e => (E e).psi.toFun) labelBits O d s C τ).2 ≤
      FPTASCost.primitiveQueries scopes d s C τ *
        (A * (1 + L + P + r * (2 * J + 3)) ^ degree) := by
  dsimp only
  have hs : 1 ≤ s := hd0.trans hd
  have hscopes : ∀ e, (E e).scope.card ≤ r := fun e => (E e).card_le
  have hparameters := PrimitiveParameters.level_precision_linear hs (by omega : 1 ≤ C) τ hτ
  refine ⟨execute_value _ _ _ _ _ _, ?_, hparameters.1, hparameters.2,
    Oracle.samplePrecision_pos _ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [execute_value]
    exact primitiveQ_error E (fun e => (O e).valueOracle) d hd hs hq hqthird hK
      hE hLip hC hqC hKC τ hτ
  · exact FPTASCost.primitiveQueries_le _ hscopes d hd τ
  · intro ν hν z i l hl j
    exact local_query_valid _ hν z i hl j
  · exact sparseExpr_operations _ hscopes _ d hd τ
  · exact PrimitiveInputHeight.sparseExpr_inputHeight_effective _ hscopes
      (fun e => (E e).psi.toFun) labelBits O hlabels d τ
  · exact execute_bitCost _ hscopes (fun e => (E e).psi.toFun) labelBits O hlabels d hd τ
  · exact FPTASOracleTime.timedSparse_time _ (fun e => (E e).psi.toFun)
      labelBits O hscopes hlabels d s C τ

end Paper08.PrimitiveAlgorithm
