import Paper37.UniformConditionalMachine
import Paper37.SpecifiedQueryBatchPeak
import Paper37.AdaptiveQueryPeak

/-! Real finite Turing machines for an explicitly supplied finite list of
conditional queries. Only that list is traversed; its binary representation
and a unary horizon pad are actual input, not an exhaustive prefix tree. -/
namespace Paper37.UniformBatchMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.WordProgram Paper37.UniformPredictionMachine Paper37.SpecifiedQueryBatch

structure BatchQuery where
  horizon : ℕ
  queries : List (List Bool)
  valid : ∀ y∈queries, y.length<horizon

def batchInputs (q : BatchQuery) : List Value := [.nat q.horizon] ++
  List.replicate 59 (.nat 0) ++ [wordsValue q.queries] ++ List.replicate q.horizon (.nat 0)

lemma batchInputs_horizon (q : BatchQuery) : inputEnv (batchInputs q) 0=.nat q.horizon := by
  simp [inputEnv,batchInputs]
lemma batchInputs_queries (q : BatchQuery) : inputEnv (batchInputs q) 60=wordsValue q.queries := by
  simp [inputEnv,batchInputs]

def decodeWordsArray : List Value → Option (List (List Bool))
  | [] => some []
  | v::vs => do let x ← decodeWordValue v; let xs ← decodeWordsArray vs; pure (x::xs)

def decodeWordsValue : Value → Option (List (List Bool))
  | .nat _ => none
  | .array vs => decodeWordsArray vs

lemma decodeWordsValue_wordsValue (qs : List (List Bool)) : decodeWordsValue (wordsValue qs)=some qs := by
  change decodeWordsArray (qs.map wordValue)=some qs
  induction qs with
  | nil => rfl
  | cons x xs ih => simp [decodeWordsArray,decodeWordValue_wordValue,ih]

def decodeBatchInputs (xs : List Value) : Option BatchQuery := do
  let qs ← decodeWordsValue (inputEnv xs 60)
  let H := (inputEnv xs 0).natVal
  if h : ∀ y∈qs,y.length<H then some ⟨H,qs,h⟩ else none

lemma decodeBatchInputs_encode (q : BatchQuery) : decodeBatchInputs (batchInputs q)=some q := by
  simp [decodeBatchInputs,batchInputs_queries,batchInputs_horizon,decodeWordsValue_wordsValue,Value.natVal]
  exact q.valid

def batchEncoding : Computability.FinEncoding BatchQuery where
  Γ := Bool
  encode q := inputEncoding.encode (batchInputs q)
  decode bs := (inputEncoding.decode bs).bind decodeBatchInputs
  decode_encode q := by simp [inputEncoding.decode_encode,decodeBatchInputs_encode]
  ΓFin := inferInstance

/-- Both horizon and supplied-list length are bounded by the actual bit input;
the entire nested query-array representation is also explicitly charged. -/
lemma batchEncoding_length (q : BatchQuery) :
    q.horizon≤(batchEncoding.encode q).length ∧
    q.queries.length≤(batchEncoding.encode q).length ∧
    (wordsValue q.queries).representationSize≤(batchEncoding.encode q).length ∧
    (batchEncoding.encode q).length≤6*q.horizon+6*q.queries.length*(q.horizon+1)+192 := by
  have hlo : q.queries.length≤(q.queries.map (fun x => (wordValue x).representationSize)).sum := by
    simpa only [List.length_map,List.map_map,Function.comp_def] using
      list_length_le_size (q.queries.map wordValue)
  have hhi:=wordsValue_size q.horizon q.queries (fun y hy => (q.valid y hy).le)
  have hH:=Paper37.DP.binarySize_le_self q.horizon
  have hlen : (batchEncoding.encode q).length =
      3*(q.horizon.size+1+59+(wordsValue q.queries).representationSize+q.horizon+2) := by
    change (inputEncoding.encode (batchInputs q)).length=_
    rw [inputEncoding_length]
    simp only [batchInputs,List.map_append,List.sum_append,List.map_replicate,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,List.sum_replicate,Value.representationSize,Nat.size_zero,zero_add,
      smul_eq_mul,Nat.mul_one]
    omega
  have hwords : q.queries.length≤(wordsValue q.queries).representationSize := by
    simpa only [wordsValue,Value.representationSize,List.map_map,Function.comp_def] using
      hlo.trans (Nat.le_add_right _ 2)
  rw [hlen]
  constructor
  · omega
  constructor
  · omega
  constructor
  · omega
  · nlinarith

def batchRun (query : Expr) (q : BatchQuery) : Value := runProgram (program query) (batchInputs q)

/-- Generic instantiation for fixed query syntax with its own proved resource
bounds. The final ordinary/adaptive theorems supply those closed facts. -/
def batchTMPoly (simulation : BoundedLoopSimulationPrinciple) (query : Expr)
    (A a r C d s : ℕ)
    (hw : ∀ (ρ : Env) (H : ℕ) (y : List Bool),ρ 0=.nat H → ρ 40=wordValue y → y.length<H → query.work ρ≤A*(H+r)^a)
    (hp : ∀ (ρ : Env) (H : ℕ) (y : List Bool),ρ 0=.nat H → ρ 40=wordValue y → y.length<H → query.peak ρ≤C*(H+s)^d) :
    Turing.TM2ComputableInPolyTime batchEncoding valueEncoding (batchRun query) := by
  let c:=compiler simulation (program query)
  exact {
    toTM2ComputableAux := c.toTM2ComputableAux
    time := timePolynomial c.constant
      (Polynomial.C 3+Polynomial.X*(Polynomial.C A*(Polynomial.X+Polynomial.C r)^a+Polynomial.C 7))
      Polynomial.X
      ((Polynomial.X+1)*(Polynomial.C C*(Polynomial.X+Polynomial.C s)^d+Polynomial.X+Polynomial.X+Polynomial.C 10))
    outputsFun := by
      intro q
      let L:=(batchEncoding.encode q).length
      have hlen:=batchEncoding_length q
      have hw0:=program_work query _ q.horizon (A*(q.horizon+r)^a) q.queries
        (batchInputs_horizon q) (batchInputs_queries q) q.valid (fun ρ y=>hw ρ q.horizon y)
      have hp0:=program_peak query _ q.horizon (C*(q.horizon+s)^d) q.queries
        (batchInputs_horizon q) (batchInputs_queries q) q.valid (fun ρ y=>hp ρ q.horizon y)
      have hw1 : (program query).work (inputEnv (batchInputs q))≤3+L*(A*(L+r)^a+7) := by
        apply hw0.trans
        apply Nat.add_le_add_left
        apply Nat.mul_le_mul hlen.2.1
        exact Nat.add_le_add_right (Nat.mul_le_mul_left A
          (Nat.pow_le_pow_left (Nat.add_le_add_right hlen.1 r) a)) 7
      have hp1 : (program query).peak (inputEnv (batchInputs q))≤(L+1)*(C*(L+s)^d+L+L+10) := by
        apply hp0.trans
        apply Nat.mul_le_mul (Nat.add_le_add_right hlen.2.1 1)
        have hmono:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left (Nat.add_le_add_right hlen.1 s) d)
        have hwords:=hlen.2.2.1
        have hcount:=hlen.2.1
        dsimp only [L]
        omega
      apply outputsInTime_mono (c.outputs (batchInputs q))
      rw [timePolynomial_eval]
      simp only [Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_mul,Polynomial.eval_pow,
        Polynomial.eval_X,Polynomial.eval_one]
      apply Nat.mul_le_mul_left
      exact executionBudget_le (program query) (batchInputs q) _ _ _ hw1 (le_refl _) hp1 }

def standardBatchTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime batchEncoding valueEncoding
      (batchRun Paper37.IntegerPredictorProgram.conditionalProgram) :=
  batchTMPoly simulation Paper37.IntegerPredictorProgram.conditionalProgram 2500 4 1 1000000000000 12 2
    Paper37.IntegerPredictorProgram.conditionalProgram_work
    Paper37.IntegerQueryProgramPeak.conditionalProgram_peak

lemma standardBatch_exact (q : BatchQuery) :
    batchRun Paper37.IntegerPredictorProgram.conditionalProgram q =
      .array (q.queries.map (fun y => pairValue (Paper37.IntegerPredictor.conditionalPair q.horizon y))) :=
  standard_eval _ _ _ (batchInputs_horizon q) (batchInputs_queries q) q.valid

/-- One real finite polynomial-time TM traverses exactly the supplied ordinary
queries and emits their exact rational pairs; no full-tree enumeration occurs. -/
theorem actualSpecifiedBatch_polytime (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime batchEncoding valueEncoding
      (batchRun Paper37.IntegerPredictorProgram.conditionalProgram),
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ q : BatchQuery, batchRun Paper37.IntegerPredictorProgram.conditionalProgram q =
        .array (q.queries.map (fun y => pairValue (Paper37.IntegerPredictor.conditionalPair q.horizon y)))) :=
  ⟨standardBatchTMPoly simulation,(compiler simulation (program Paper37.IntegerPredictorProgram.conditionalProgram)).finiteAlphabets,
    standardBatch_exact⟩

def adaptiveBatchTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime batchEncoding valueEncoding
      (batchRun Paper37.AdaptiveQueryProgram.conditionalProgram) :=
  batchTMPoly simulation Paper37.AdaptiveQueryProgram.conditionalProgram 5100 5 1 1000000000000000000 20 2
    Paper37.AdaptiveQueryProgram.conditionalProgram_work
    Paper37.AdaptiveQueryPeak.conditionalProgram_peak

lemma adaptiveBatch_exact (q : BatchQuery) :
    batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q =
      .array (q.queries.map (fun y => pairValue (Paper37.AdaptiveIntegerOutput.conditionalPair q.horizon y))) :=
  adaptive_eval _ _ _ (batchInputs_horizon q) (batchInputs_queries q) q.valid

/-- The exact mix-before-ratio adaptive conditional is likewise computed for
precisely the explicitly supplied list by one genuine finite polynomial TM. -/
theorem actualAdaptiveSpecifiedBatch_polytime (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime batchEncoding valueEncoding
      (batchRun Paper37.AdaptiveQueryProgram.conditionalProgram),
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ q : BatchQuery, batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q =
        .array (q.queries.map (fun y => pairValue (Paper37.AdaptiveIntegerOutput.conditionalPair q.horizon y)))) :=
  ⟨adaptiveBatchTMPoly simulation,(compiler simulation (program Paper37.AdaptiveQueryProgram.conditionalProgram)).finiteAlphabets,
    adaptiveBatch_exact⟩

def itemAt (out : Value) (i : ℕ) : Value := out.arrayVal[i]?.getD (.nat 0)
def rationalValue (out : Value) : ℚ :=
  ((out.arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/(out.arrayVal[1]?.getD (Value.nat 0)).natVal

def denominatorValue (out : Value) : ℕ := (out.arrayVal[1]?.getD (Value.nat 0)).natVal

lemma standard_item (q : BatchQuery) (i : ℕ) (hi : i<q.queries.length) :
    itemAt (batchRun Paper37.IntegerPredictorProgram.conditionalProgram q) i =
      pairValue (Paper37.IntegerPredictor.conditionalPair q.horizon q.queries[i]) := by
  rw [standardBatch_exact]
  simp [itemAt,Value.arrayVal,List.getElem?_map,List.getElem?_eq_getElem hi]

lemma adaptive_item (q : BatchQuery) (i : ℕ) (hi : i<q.queries.length) :
    itemAt (batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q) i =
      pairValue (Paper37.AdaptiveIntegerOutput.conditionalPair q.horizon q.queries[i]) := by
  rw [adaptiveBatch_exact]
  simp [itemAt,Value.arrayVal,List.getElem?_map,List.getElem?_eq_getElem hi]

/-- Every actual ordinary output item is a valid positive-denominator rational
encoding of the requested source conditional. -/
theorem standard_item_correct (q : BatchQuery) (i : ℕ) (hi : i<q.queries.length) :
    0<denominatorValue (itemAt (batchRun Paper37.IntegerPredictorProgram.conditionalProgram q) i) ∧
    rationalValue (itemAt (batchRun Paper37.IntegerPredictorProgram.conditionalProgram q) i)=
      Paper37.Prediction.blockConditional q.horizon q.queries[i] := by
  rw [standard_item q i hi]
  exact ⟨Paper37.IntegerPredictor.conditionalPair_denominator_pos _ _ (q.valid _ (List.getElem_mem hi)),
    Paper37.IntegerPredictor.conditionalPair_exact _ _ (q.valid _ (List.getElem_mem hi))⟩

/-- Every actual adaptive output item is the ratio after mixture, as required
by E.3; no mixture of separately normalized conditionals is substituted. -/
theorem adaptive_item_correct (q : BatchQuery) (i : ℕ) (hi : i<q.queries.length) :
    0<denominatorValue (itemAt (batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q) i) ∧
    rationalValue (itemAt (batchRun Paper37.AdaptiveQueryProgram.conditionalProgram q) i)=
      Paper37.Adaptive.adaptiveConditional q.horizon q.queries[i] := by
  rw [adaptive_item q i hi]
  exact ⟨Paper37.AdaptiveIntegerOutput.conditionalPair_denominator_pos _ _ (q.valid _ (List.getElem_mem hi)),
    Paper37.AdaptiveIntegerOutput.conditionalPair_exact _ _ (q.valid _ (List.getElem_mem hi))⟩

end
end Paper37.UniformBatchMachine
