import Paper37.UniformPredictionMachine

/-! Explicit horizon-padded binary input for every admissible continuation
query. Padding makes a numerical horizon polynomial in encoded input length. -/
namespace Paper37.UniformQueryMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.WordProgram Paper37.IntegerPredictorProgram Paper37.UniformPredictionMachine

structure Query where
  horizon : ℕ
  word : List Bool
  remaining : ℕ
  budget : word.length+remaining≤horizon

/-- Slots0=horizon,12=remaining,40=word. The final horizon-many zero values
are explicit unary padding; the algorithm does not read those extra slots. -/
def queryInputs (q : Query) : List Value :=
  [.nat q.horizon] ++ List.replicate 11 (.nat 0) ++ [.nat q.remaining] ++
    List.replicate 27 (.nat 0) ++ [wordValue q.word] ++ List.replicate q.horizon (.nat 0)

lemma queryInputs_horizon (q : Query) : inputEnv (queryInputs q) 0=.nat q.horizon := by
  simp [inputEnv,queryInputs]
lemma queryInputs_remaining (q : Query) : inputEnv (queryInputs q) 12=.nat q.remaining := by
  simp [inputEnv,queryInputs]
lemma queryInputs_word (q : Query) : inputEnv (queryInputs q) 40=wordValue q.word := by
  simp [inputEnv,queryInputs]

/-- All semantic side conditions are checked by the executable query decoder. -/
def decodeQueryInputs (xs : List Value) : Option Query := do
  let word ← decodeWordValue (inputEnv xs 40)
  let H := (inputEnv xs 0).natVal
  let R := (inputEnv xs 12).natVal
  if h : word.length+R≤H then some ⟨H,word,R,h⟩ else none

lemma decodeQueryInputs_queryInputs (q : Query) : decodeQueryInputs (queryInputs q)=some q := by
  simp [decodeQueryInputs,queryInputs_word,queryInputs_horizon,queryInputs_remaining,
    decodeWordValue_wordValue,Value.natVal,q.budget]

def queryEncoding : Computability.FinEncoding Query where
  Γ := Bool
  encode q := inputEncoding.encode (queryInputs q)
  decode bs := (inputEncoding.decode bs).bind decodeQueryInputs
  decode_encode q := by simp [inputEncoding.decode_encode,decodeQueryInputs_queryInputs]
  ΓFin := inferInstance

lemma queryEncoding_length (q : Query) :
    q.horizon ≤ (queryEncoding.encode q).length ∧
      (queryEncoding.encode q).length≤15*q.horizon+132 := by
  change q.horizon ≤ (inputEncoding.encode (queryInputs q)).length ∧
    (inputEncoding.encode (queryInputs q)).length≤15*q.horizon+132
  rw [inputEncoding_length]
  simp only [queryInputs,List.map_append,List.sum_append,List.map_replicate,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,List.sum_replicate,Value.representationSize,
    Nat.size_zero,zero_add,smul_eq_mul,Nat.mul_one,Nat.add_zero]
  have hword := wordValue_representationSize q.word
  have hH : q.horizon.size≤q.horizon := Nat.size_le.mpr q.horizon.lt_two_pow_self
  have hR : q.remaining.size≤q.remaining := Nat.size_le.mpr q.remaining.lt_two_pow_self
  have hb := q.budget
  omega

def queryRun (q : Query) : Value := runProgram continuationProgram (queryInputs q)

lemma queryRun_eq_pair (q : Query) :
    queryRun q=pairValue (Paper37.CachedOutput.evaluatePair q.horizon q.word q.remaining) :=
  continuationProgram_eval _ _ _ _ (queryInputs_horizon q) (queryInputs_word q)
    (queryInputs_remaining q) q.budget

/-- All admissible continuation outputs use a genuine positive denominator. -/
lemma queryRun_denominator_pos (q : Query) :
    0<((queryRun q).arrayVal[1]?.getD (Value.nat 0)).natVal := by
  rw [queryRun_eq_pair,Paper37.CachedOutput.evaluatePair_eq _ _ _ q.budget]
  exact Paper37.DP.commonDenominator_pos q.horizon

/-- The fixed program's exact integer pair computes the source continuation C.8. -/
theorem queryRun_exact (q : Query) :
    (((queryRun q).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
      ((queryRun q).arrayVal[1]?.getD (Value.nat 0)).natVal =
      Paper37.Prediction.continuationMass (q.word.length+q.remaining) q.word := by
  rw [queryRun_eq_pair]
  exact Paper37.CachedOutput.evaluatePair_correct q.horizon q.word q.remaining q.budget

lemma query_work (q : Query) :
    continuationProgram.work (inputEnv (queryInputs q))≤1000*(q.horizon+1)^4 :=
  continuationProgram_work _ _ _ _ (queryInputs_horizon q) (queryInputs_word q)
    (queryInputs_remaining q) q.budget

lemma query_work_encoding (q : Query) :
    continuationProgram.work (inputEnv (queryInputs q))≤1000*((queryEncoding.encode q).length+1)^4 :=
  (query_work q).trans (Nat.mul_le_mul_left 1000
    (Nat.pow_le_pow_left (Nat.add_le_add_right (queryEncoding_length q).1 1) 4))

def queryMachine (simulation : BoundedLoopSimulationPrinciple) : Compilation continuationProgram :=
  compiler simulation continuationProgram

def queryTMComputable (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2Computable queryEncoding valueEncoding queryRun where
  toTM2ComputableAux := (queryMachine simulation).toTM2ComputableAux
  outputsFun q := ((queryMachine simulation).outputs (queryInputs q)).toTM2Outputs

theorem queryTM_exists (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2Computable queryEncoding valueEncoding queryRun,
      ∀ k : M.tm.K, Finite (M.tm.Γ k) :=
  ⟨queryTMComputable simulation,(queryMachine simulation).finiteAlphabets⟩

def zeroQuery : Query := ⟨0,[],0,by simp⟩

/-- This is the actual finite zero-horizon execution peak, used as one fixed
polynomial coefficient. No large numerical certificate is generated. -/
def zeroQueryPeak : ℕ := continuationProgram.peak (inputEnv (queryInputs zeroQuery))

lemma query_zero_peak (q : Query) (hH : q.horizon=0) :
    continuationProgram.peak (inputEnv (queryInputs q))=zeroQueryPeak := by
  have hb := q.budget
  have hword : q.word=[] := List.length_eq_zero_iff.mp (by omega)
  have hR : q.remaining=0 := by omega
  simp only [zeroQueryPeak,queryInputs,hH,hword,hR,zeroQuery]

private lemma peak_encoding_of_positive (C d : ℕ)
    (hpeak : ∀ q : Query, 0<q.horizon → continuationProgram.peak (inputEnv (queryInputs q))≤C*(q.horizon+2)^d)
    (q : Query) : continuationProgram.peak (inputEnv (queryInputs q))≤
      (C+zeroQueryPeak)*((queryEncoding.encode q).length+2)^d := by
  by_cases hH : q.horizon=0
  · rw [query_zero_peak q hH]
    have hone : 1≤((queryEncoding.encode q).length+2)^d := by
      have hpos : 0<((queryEncoding.encode q).length+2)^d := Nat.pow_pos (by omega)
      omega
    exact (Nat.le_add_left zeroQueryPeak C).trans (by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (C+zeroQueryPeak) hone)
  · exact (hpeak q (by omega)).trans (Nat.mul_le_mul
      (Nat.le_add_right C zeroQueryPeak)
      (Nat.pow_le_pow_left (Nat.add_le_add_right (queryEncoding_length q).1 2) d))

private def polyMachineOfPositivePeak (simulation : BoundedLoopSimulationPrinciple)
    (C d : ℕ) (hpeak : ∀ q : Query, 0<q.horizon →
      continuationProgram.peak (inputEnv (queryInputs q))≤C*(q.horizon+2)^d) :
    Turing.TM2ComputableInPolyTime queryEncoding valueEncoding queryRun where
  toTM2ComputableAux := (queryMachine simulation).toTM2ComputableAux
  time := timePolynomial (queryMachine simulation).constant
    (Polynomial.C 1000*(Polynomial.X+1)^4) Polynomial.X
    (Polynomial.C (C+zeroQueryPeak)*(Polynomial.X+Polynomial.C 2)^d)
  outputsFun q := by
    apply outputsInTime_mono ((queryMachine simulation).outputs (queryInputs q))
    rw [timePolynomial_eval]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    apply Nat.mul_le_mul_left
    apply executionBudget_le
    · exact query_work_encoding q
    · exact le_refl _
    · exact peak_encoding_of_positive C d hpeak q

/-- The concrete finite query AST has polynomial work and dynamic peak on
all admissible inputs, including the separately absorbed zero-horizon run. -/
def queryTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime queryEncoding valueEncoding queryRun :=
  polyMachineOfPositivePeak simulation 1000000000000 12 (fun q hpos => by
    exact Paper37.IntegerQueryProgramPeak.continuationProgram_peak _ _ _ _ hpos
      (queryInputs_horizon q) (queryInputs_word q) (queryInputs_remaining q) q.budget)

theorem queryTM_poly_exists (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime queryEncoding valueEncoding queryRun,
      ∀ k : M.tm.K, Finite (M.tm.Γ k) :=
  ⟨queryTMPoly simulation,(queryMachine simulation).finiteAlphabets⟩

/-- A single actual finite polynomial-time TM computes every source C.8
continuation query, with exact rational output and a positive denominator. -/
theorem actualContinuation_polytime (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime queryEncoding valueEncoding queryRun,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ q : Query, 0<((queryRun q).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀ q : Query, (((queryRun q).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
        ((queryRun q).arrayVal[1]?.getD (Value.nat 0)).natVal =
        Paper37.Prediction.continuationMass (q.word.length+q.remaining) q.word) :=
  ⟨queryTMPoly simulation,(queryMachine simulation).finiteAlphabets,
    queryRun_denominator_pos,queryRun_exact⟩

end
end Paper37.UniformQueryMachine
