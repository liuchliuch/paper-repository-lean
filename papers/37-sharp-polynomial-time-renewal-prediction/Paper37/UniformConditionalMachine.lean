import Paper37.UniformQueryMachine

/-! Exact standard conditional-query C.4 as a single real finite polynomial
Turing machine, on an explicit horizon-padded binary input. -/
namespace Paper37.UniformConditionalMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.UniformQueryMachine Paper37.UniformPredictionMachine Paper37.WordProgram
open Paper37.IntegerPredictorProgram

structure ConditionalQuery where
  horizon : ℕ
  word : List Bool
  short : word.length<horizon

def queryData (q : ConditionalQuery) : Query := ⟨q.horizon,q.word,0,by simpa using q.short.le⟩
def conditionalInputs (q : ConditionalQuery) : List Value := queryInputs (queryData q)

def decodeConditionalInputs (xs : List Value) : Option ConditionalQuery := do
  let word ← decodeWordValue (inputEnv xs 40)
  let H := (inputEnv xs 0).natVal
  if h : word.length<H then some ⟨H,word,h⟩ else none

lemma decodeConditionalInputs_encode (q : ConditionalQuery) :
    decodeConditionalInputs (conditionalInputs q)=some q := by
  simp [decodeConditionalInputs,conditionalInputs,queryInputs_word,queryInputs_horizon,
    decodeWordValue_wordValue,queryData,Value.natVal,q.short]

def conditionalEncoding : Computability.FinEncoding ConditionalQuery where
  Γ := Bool
  encode q := inputEncoding.encode (conditionalInputs q)
  decode bs := (inputEncoding.decode bs).bind decodeConditionalInputs
  decode_encode q := by simp [inputEncoding.decode_encode,decodeConditionalInputs_encode]
  ΓFin := inferInstance

lemma conditionalEncoding_length (q : ConditionalQuery) :
    q.horizon≤(conditionalEncoding.encode q).length ∧
      (conditionalEncoding.encode q).length≤15*q.horizon+132 := queryEncoding_length (queryData q)

def conditionalRun (q : ConditionalQuery) : Value := runProgram conditionalProgram (conditionalInputs q)

lemma conditionalRun_eq_pair (q : ConditionalQuery) :
    conditionalRun q=pairValue (Paper37.IntegerPredictor.conditionalPair q.horizon q.word) :=
  conditionalProgram_eval _ _ _ (queryInputs_horizon (queryData q)) (queryInputs_word (queryData q)) q.short

lemma conditionalRun_denominator_pos (q : ConditionalQuery) :
    0<((conditionalRun q).arrayVal[1]?.getD (Value.nat 0)).natVal := by
  rw [conditionalRun_eq_pair]
  exact Paper37.IntegerPredictor.conditionalPair_denominator_pos q.horizon q.word q.short

lemma conditionalRun_exact (q : ConditionalQuery) :
    (((conditionalRun q).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
      ((conditionalRun q).arrayVal[1]?.getD (Value.nat 0)).natVal =
      Paper37.Prediction.blockConditional q.horizon q.word := by
  rw [conditionalRun_eq_pair]
  exact Paper37.IntegerPredictor.conditionalPair_exact q.horizon q.word q.short

/-- Actual C.4 machine, with no program-specific work, peak, or encoding input. -/
def conditionalTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime conditionalEncoding valueEncoding conditionalRun := by
  let c:=compiler simulation conditionalProgram
  exact {
    toTM2ComputableAux := c.toTM2ComputableAux
    time := timePolynomial c.constant (Polynomial.C 2500*(Polynomial.X+1)^4) Polynomial.X
      (Polynomial.C 1000000000000*(Polynomial.X+Polynomial.C 2)^12)
    outputsFun := by
      intro q
      apply outputsInTime_mono (c.outputs (conditionalInputs q))
      rw [timePolynomial_eval]
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
        Polynomial.eval_one,Polynomial.eval_X]
      apply Nat.mul_le_mul_left
      apply executionBudget_le
      · have hw:=conditionalProgram_work _ q.horizon q.word
          (queryInputs_horizon (queryData q)) (queryInputs_word (queryData q)) q.short
        exact hw.trans (Nat.mul_le_mul_left 2500
          (Nat.pow_le_pow_left (Nat.add_le_add_right (conditionalEncoding_length q).1 1) 4))
      · exact le_refl _
      · have hp:=Paper37.IntegerQueryProgramPeak.conditionalProgram_peak _ q.horizon q.word
          (queryInputs_horizon (queryData q)) (queryInputs_word (queryData q)) q.short
        exact hp.trans (Nat.mul_le_mul_left 1000000000000
          (Nat.pow_le_pow_left (Nat.add_le_add_right (conditionalEncoding_length q).1 2) 12)) }

theorem actualConditional_polytime (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime conditionalEncoding valueEncoding conditionalRun,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ q : ConditionalQuery, 0<((conditionalRun q).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀ q : ConditionalQuery, (((conditionalRun q).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
        ((conditionalRun q).arrayVal[1]?.getD (Value.nat 0)).natVal =
        Paper37.Prediction.blockConditional q.horizon q.word) :=
  ⟨conditionalTMPoly simulation,(compiler simulation conditionalProgram).finiteAlphabets,
    conditionalRun_denominator_pos,conditionalRun_exact⟩

end
end Paper37.UniformConditionalMachine
