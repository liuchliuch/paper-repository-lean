import Paper37.UniformAdaptivePredictionMachine
import Paper37.UniformQueryMachine

/-! Actual finite polynomial-time Turing machines for every admissible
adaptive prefix mass and conditional query. Numerical horizons are explicitly
padded in the binary input, and all semantic side conditions are decoded. -/
namespace Paper37.UniformAdaptiveQueryMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.WordProgram Paper37.AdaptiveQueryProgram

/-- `strict=false` requests a prefix mass; `strict=true` requests a next-bit
conditional before its horizon. Both cover every positive horizon. -/
structure Request (strict:Bool) where
  horizon:ℕ
  word:List Bool
  positive:0<horizon
  budget:word.length+(if strict then 1 else 0)≤horizon

lemma Request.proper (q:Request true) : q.word.length<q.horizon := by
  have hb:q.word.length+1≤q.horizon := by simpa using q.budget
  omega

def asQuery {strict:Bool} (q:Request strict) : Paper37.UniformQueryMachine.Query :=
  ⟨q.horizon,q.word,0,by have hb:=q.budget;omega⟩

def requestInputs {strict:Bool} (q:Request strict) : List Value :=
  Paper37.UniformQueryMachine.queryInputs (asQuery q)

lemma requestInputs_horizon {strict:Bool} (q:Request strict) :
    inputEnv (requestInputs q) 0=.nat q.horizon :=
  Paper37.UniformQueryMachine.queryInputs_horizon (asQuery q)
lemma requestInputs_word {strict:Bool} (q:Request strict) :
    inputEnv (requestInputs q) 40=wordValue q.word :=
  Paper37.UniformQueryMachine.queryInputs_word (asQuery q)

def decodeRequestInputs (strict:Bool) (xs:List Value) : Option (Request strict) := do
  let word←Paper37.UniformPredictionMachine.decodeWordValue (inputEnv xs 40)
  let H:=(inputEnv xs 0).natVal
  if hp:0<H then
    if hb:word.length+(if strict then 1 else 0)≤H then some ⟨H,word,hp,hb⟩ else none
  else none

lemma decodeRequestInputs_requestInputs (strict:Bool) (q:Request strict) :
    decodeRequestInputs strict (requestInputs q)=some q := by
  simp [decodeRequestInputs,requestInputs_word,requestInputs_horizon,
    Paper37.UniformPredictionMachine.decodeWordValue_wordValue,Value.natVal,q.positive,q.budget]

def requestEncoding (strict:Bool) : Computability.FinEncoding (Request strict) where
  Γ:=Bool
  encode q:=inputEncoding.encode (requestInputs q)
  decode bs:=(inputEncoding.decode bs).bind (decodeRequestInputs strict)
  decode_encode q:=by simp [inputEncoding.decode_encode,decodeRequestInputs_requestInputs]
  ΓFin:=inferInstance

/-- The explicit input consists of the horizon, word, fixed-register overhead
and horizon-many padding cells. Its length is linear in the numerical horizon. -/
lemma requestEncoding_length {strict:Bool} (q:Request strict) :
    q.horizon≤((requestEncoding strict).encode q).length ∧
      ((requestEncoding strict).encode q).length≤15*q.horizon+132 :=
  Paper37.UniformQueryMachine.queryEncoding_length (asQuery q)

def requestProgram (strict:Bool) : Expr := if strict then conditionalProgram else prefixProgram

def requestRun (strict:Bool) (q:Request strict) : Value :=
  runProgram (requestProgram strict) (requestInputs q)

def requestPair (strict:Bool) (q:Request strict) : ℕ×ℕ :=
  if strict then Paper37.AdaptiveIntegerOutput.conditionalPair q.horizon q.word
  else Paper37.AdaptiveIntegerOutput.prefixPair q.horizon q.word

lemma requestRun_eq_pair (strict:Bool) (q:Request strict) :
    requestRun strict q=pairValue (requestPair strict q) := by
  cases strict with
  | false =>
    exact prefixProgram_eval _ q.horizon q.word (requestInputs_horizon q) (requestInputs_word q)
      (by simpa using q.budget)
  | true =>
    exact conditionalProgram_eval _ q.horizon q.word (requestInputs_horizon q) (requestInputs_word q)
      q.proper

def sourceQuery (strict:Bool) (q:Request strict) : ℚ :=
  if strict then Paper37.Adaptive.adaptiveConditional q.horizon q.word
  else Paper37.Adaptive.adaptivePrefix q.horizon q.word

/-- Every actual integer-only query result equals the original source mass
or source conditional on all requested admissible prefixes. -/
theorem requestRun_exact (strict:Bool) (q:Request strict) :
    (((requestRun strict q).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
      ((requestRun strict q).arrayVal[1]?.getD (Value.nat 0)).natVal=sourceQuery strict q := by
  rw [requestRun_eq_pair]
  cases strict with
  | false =>
    exact Paper37.AdaptiveIntegerOutput.prefixPair_exact q.horizon q.word q.positive
      (by simpa using q.budget)
  | true =>
    exact Paper37.AdaptiveIntegerOutput.conditionalPair_exact q.horizon q.word
      q.proper

lemma requestRun_denominator_pos (strict:Bool) (q:Request strict) :
    0<((requestRun strict q).arrayVal[1]?.getD (Value.nat 0)).natVal := by
  rw [requestRun_eq_pair]
  cases strict with
  | false =>
    exact Paper37.AdaptiveIntegerOutput.prefixPair_denominator_pos q.horizon q.word q.positive
      (by simpa using q.budget)
  | true =>
    exact Paper37.AdaptiveIntegerOutput.conditionalPair_denominator_pos q.horizon q.word
      q.proper

lemma request_work (strict:Bool) (q:Request strict) :
    (requestProgram strict).work (inputEnv (requestInputs q))≤5100*(q.horizon+1)^5 := by
  cases strict with
  | false =>
    exact (prefixProgram_work _ q.horizon q.word (requestInputs_horizon q) (requestInputs_word q)
      (by simpa using q.budget)).trans (Nat.mul_le_mul_right _ (by decide))
  | true =>
    exact conditionalProgram_work _ q.horizon q.word (requestInputs_horizon q) (requestInputs_word q)
      q.proper

lemma request_peak (strict:Bool) (q:Request strict) :
    (requestProgram strict).peak (inputEnv (requestInputs q))≤10^18*(q.horizon+2)^20 := by
  cases strict with
  | false =>
    exact Paper37.AdaptiveQueryPeak.prefixProgram_peak _ q.horizon q.word q.positive
      (requestInputs_horizon q) (requestInputs_word q) (by simpa using q.budget)
  | true =>
    exact Paper37.AdaptiveQueryPeak.conditionalProgram_peak _ q.horizon q.word
      (requestInputs_horizon q) (requestInputs_word q)
      q.proper

def requestMachine (simulation:BoundedLoopSimulationPrinciple) (strict:Bool) :
    Compilation (requestProgram strict) := compiler simulation (requestProgram strict)

/-- Each of the two fixed programs has a true finite-alphabet Turing-machine
realization with a polynomial bound in its actual binary input length. -/
def requestTMPoly (simulation:BoundedLoopSimulationPrinciple) (strict:Bool) :
    Turing.TM2ComputableInPolyTime (requestEncoding strict) valueEncoding (requestRun strict) where
  toTM2ComputableAux:=(requestMachine simulation strict).toTM2ComputableAux
  time:=timePolynomial (requestMachine simulation strict).constant
    (Polynomial.C 5100*(Polynomial.X+1)^5) Polynomial.X
    (Polynomial.C (10^18)*(Polynomial.X+Polynomial.C 2)^20)
  outputsFun q:=by
    apply outputsInTime_mono ((requestMachine simulation strict).outputs (requestInputs q))
    rw [timePolynomial_eval]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    apply Nat.mul_le_mul_left
    apply executionBudget_le
    · exact (request_work strict q).trans (Nat.mul_le_mul_left 5100
        (Nat.pow_le_pow_left (Nat.add_le_add_right (requestEncoding_length q).1 1) 5))
    · exact le_refl _
    · exact (request_peak strict q).trans (Nat.mul_le_mul_left (10^18)
        (Nat.pow_le_pow_left (Nat.add_le_add_right (requestEncoding_length q).1 2) 20))

/-- Exact output, positive denominator, and polynomial machine complexity hold
for every prefix query, including every member of any specified finite batch. -/
theorem actualQuery_polytime (simulation:BoundedLoopSimulationPrinciple) (strict:Bool) :
    ∃M:Turing.TM2ComputableInPolyTime (requestEncoding strict) valueEncoding (requestRun strict),
      (∀k:M.tm.K,Finite (M.tm.Γ k)) ∧
      (∀q:Request strict,0<((requestRun strict q).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀q:Request strict,(((requestRun strict q).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
        ((requestRun strict q).arrayVal[1]?.getD (Value.nat 0)).natVal=sourceQuery strict q) :=
  ⟨requestTMPoly simulation strict,(requestMachine simulation strict).finiteAlphabets,
    requestRun_denominator_pos strict,requestRun_exact strict⟩

end
end Paper37.UniformAdaptiveQueryMachine
