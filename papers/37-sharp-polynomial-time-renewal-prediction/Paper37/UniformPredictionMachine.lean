import Paper37.BoundedLoopMachine
import Paper37.IntegerPredictorProgram
import Paper37.IntegerPredictorProgramWork
import Paper37.IntegerPredictorProgramPeak

/-! Concrete binary inputs and the actual fixed predictor program's finite
Turing-machine realization. The source word is the sole varying input. -/
namespace Paper37.UniformPredictionMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.WordProgram Paper37.IntegerPredictorProgram

/-- Exactly 41 initial registers: slots 0,...,39 are zero and slot 40 contains
the observed binary word. The source program computes its horizon internally. -/
def sourceInputs (x : List Bool) : List Value := List.replicate 40 (.nat 0) ++ [wordValue x]

lemma sourceInputs_length (x : List Bool) : (sourceInputs x).length=41 := by simp [sourceInputs]

lemma sourceInputs_word (x : List Bool) : inputEnv (sourceInputs x) 40=wordValue x := by
  simp [inputEnv,sourceInputs]

def decodeBitValue : Value → Option Bool
  | .nat 0 => some false
  | .nat 1 => some true
  | _ => none

def decodeWordArray : List Value → Option (List Bool)
  | [] => some []
  | v::vs => do let b ← decodeBitValue v; let bs ← decodeWordArray vs; pure (b::bs)

def decodeWordValue : Value → Option (List Bool)
  | .nat _ => none
  | .array vs => decodeWordArray vs

lemma decodeWordValue_wordValue (x : List Bool) : decodeWordValue (wordValue x)=some x := by
  change decodeWordArray (x.map bitValue)=some x
  induction x with
  | nil => rfl
  | cons b x ih => cases b <;> simp [bitValue,decodeWordArray,decodeBitValue,ih]

/-- The input is a fully specified bit string; its executable decoder reads
the finite input array and the binary word in its designated slot. -/
def sourceEncoding : Computability.FinEncoding (List Bool) where
  Γ := Bool
  encode x := inputEncoding.encode (sourceInputs x)
  decode bs := (inputEncoding.decode bs).bind (fun xs => decodeWordValue (inputEnv xs 40))
  decode_encode x := by simp [inputEncoding.decode_encode,sourceInputs_word,decodeWordValue_wordValue]
  ΓFin := inferInstance

lemma wordValue_representationSize (x : List Bool) :
    x.length+2 ≤ (wordValue x).representationSize ∧
      (wordValue x).representationSize ≤ 2*x.length+2 := by
  have hsum : x.length ≤ (x.map (fun b => (bitValue b).representationSize)).sum ∧
      (x.map (fun b => (bitValue b).representationSize)).sum ≤ 2*x.length := by
    induction x with
    | nil => simp
    | cons b x ih =>
      have hb : 1 ≤ (bitValue b).representationSize ∧ (bitValue b).representationSize≤2 := by
        cases b <;> simp [bitValue,Value.representationSize]
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      omega
  simpa only [wordValue,Value.representationSize,List.map_map,Function.comp_def] using
    And.intro (Nat.add_le_add_right hsum.1 2) (Nat.add_le_add_right hsum.2 2)

/-- The complete nested-array bit encoding has fixed overhead 132 bits and
between three and six bits per observed source bit. -/
theorem sourceEncoding_length (x : List Bool) :
    3*x.length+132 ≤ (sourceEncoding.encode x).length ∧
      (sourceEncoding.encode x).length ≤ 6*x.length+132 := by
  change 3*x.length+132 ≤ (inputEncoding.encode (sourceInputs x)).length ∧
    (inputEncoding.encode (sourceInputs x)).length≤6*x.length+132
  rw [inputEncoding_length]
  simp only [sourceInputs,List.map_append,List.sum_append,List.map_replicate,
    Value.representationSize,Nat.size_zero,zero_add,List.sum_replicate,List.map_cons,
    List.map_nil,List.sum_cons,List.sum_nil,smul_eq_mul,Nat.mul_one]
  have h := wordValue_representationSize x
  omega

lemma sourceLength_le_encoding (x : List Bool) : x.length ≤ (sourceEncoding.encode x).length := by
  have h := (sourceEncoding_length x).1
  omega

/-- Exact output of the fixed bounded-loop AST on its concrete source input. -/
def sourceRun (x : List Bool) : Value := runProgram predictorProgram (sourceInputs x)

lemma sourceRun_eq_pair (x : List Bool) :
    sourceRun x=pairValue (Paper37.IntegerPredictor.predictorPair x.length x) :=
  predictorProgram_eval _ x (sourceInputs_word x)

/-- The natural pair emitted by the actual algorithm denotes exactly the
paper's rational source predictor for every history, including the empty one. -/
theorem sourceRun_exact (x : List Bool) :
    (((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
      ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal = Paper37.Prediction.predict x.length x :=
  predictorProgram_source _ x (sourceInputs_word x)

/-- Every nonempty source history produces a valid positive-denominator
rational representation, rather than relying on totalized division by zero. -/
theorem sourceRun_denominator_pos (x : List Bool) (hx : 0<x.length) :
    0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal := by
  rw [sourceRun_eq_pair]
  change 0<(Paper37.IntegerPredictor.predictorPair x.length x).2
  change 0<(Paper37.IntegerOutput.pairSum (Paper37.IntegerPredictor.suffixPairs x.length x)).2*x.length
  apply Nat.mul_pos _ hx
  apply Paper37.IntegerOutput.pairSum_denominator_pos
  intro p hp
  obtain ⟨t,rfl⟩ := List.mem_ofFn.mp hp
  apply Paper37.IntegerPredictor.conditionalPair_denominator_pos
  simp only [List.length_drop]
  omega

/-- The source syntax's own established operation count on its concrete input. -/
lemma source_work (x : List Bool) :
    predictorProgram.work (inputEnv (sourceInputs x)) ≤ 3000*(x.length+2)^5 :=
  predictorProgram_work _ x (sourceInputs_word x)

/-- The same operation count is polynomial in the actual encoded input length. -/
lemma source_work_encoding (x : List Bool) :
    predictorProgram.work (inputEnv (sourceInputs x)) ≤
      3000*((sourceEncoding.encode x).length+2)^5 := by
  exact (source_work x).trans (Nat.mul_le_mul_left 3000
    (Nat.pow_le_pow_left (Nat.add_le_add_right (sourceLength_le_encoding x) 2) 5))

/-- The compiled machine uses one fixed finite program for all word lengths;
its time certificate is the evaluator's actual dynamic work and peak. -/
def sourceMachine (simulation : BoundedLoopSimulationPrinciple) : Compilation predictorProgram :=
  compiler simulation predictorProgram

def sourceTMComputable (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2Computable sourceEncoding valueEncoding sourceRun where
  toTM2ComputableAux := (sourceMachine simulation).toTM2ComputableAux
  outputsFun x := ((sourceMachine simulation).outputs (sourceInputs x)).toTM2Outputs

/-- A bona fide finite machine already computes the exact integer output. The
sole external input is generic over all bounded-loop syntax and all inputs. -/
theorem sourceTM_exists (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2Computable sourceEncoding valueEncoding sourceRun,
      ∀ k : M.tm.K, Finite (M.tm.Γ k) :=
  ⟨sourceTMComputable simulation,(sourceMachine simulation).finiteAlphabets⟩

/-- Pointwise certificate on the actual source input, retaining the same TM
and the exact binary output rather than a scalar operation-count assertion. -/
def sourceMachine_outputs (simulation : BoundedLoopSimulationPrinciple) (x : List Bool) :
    Turing.TM2OutputsInTime (sourceMachine simulation).tm
      (List.map (sourceMachine simulation).inputAlphabet.invFun (sourceEncoding.encode x))
      (some (List.map (sourceMachine simulation).outputAlphabet.invFun (valueEncoding.encode (sourceRun x))))
      ((sourceMachine simulation).constant * executionBudget predictorProgram (sourceInputs x)) :=
  (sourceMachine simulation).outputs (sourceInputs x)

/-- Internal transport from an actual peak theorem to the same fixed compiled
machine. The final source theorem instantiates this with the proved program
peak; the work bound and all input-encoding facts are already closed above. -/
private def polyMachineOfPeak (simulation : BoundedLoopSimulationPrinciple)
    (C d offset : ℕ) (hpeak : ∀ x : List Bool, predictorProgram.peak (inputEnv (sourceInputs x))≤C*(x.length+offset)^d) :
    Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun where
  toTM2ComputableAux := (sourceMachine simulation).toTM2ComputableAux
  time := timePolynomial (sourceMachine simulation).constant
    (Polynomial.C 3000*(Polynomial.X+Polynomial.C 2)^5) Polynomial.X
    (Polynomial.C C*(Polynomial.X+Polynomial.C offset)^d)
  outputsFun x := by
    apply outputsInTime_mono (sourceMachine_outputs simulation x)
    rw [timePolynomial_eval]
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
    apply Nat.mul_le_mul_left
    apply executionBudget_le
    · exact source_work_encoding x
    · exact le_refl _
    · exact (hpeak x).trans (Nat.mul_le_mul_left C
        (Nat.pow_le_pow_left (Nat.add_le_add_right (sourceLength_le_encoding x) offset) d))

/-- One fixed genuine finite Turing machine computes the source predictor's
exact integer output in polynomial time. Its program work and intermediate
representation bounds are established for this very AST, with no remaining
predictor-specific resource or encoding premise. -/
def sourceTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun :=
  polyMachineOfPeak simulation 100000000000000000000 13 3
    (fun x => predictorProgram_peak _ x (sourceInputs_word x))

theorem sourceTM_poly_exists (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun,
      ∀ k : M.tm.K, Finite (M.tm.Γ k) :=
  ⟨sourceTMPoly simulation,(sourceMachine simulation).finiteAlphabets⟩

theorem sourceTM_time_exists (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInTime sourceEncoding valueEncoding sourceRun,
      ∀ k : M.tm.K, Finite (M.tm.Γ k) :=
  ⟨(sourceTMPoly simulation).toTM2ComputableInTime,(sourceMachine simulation).finiteAlphabets⟩

/-- The complete computational statement: an actual finite polynomial-time TM
emits valid rational pairs on nonempty histories and their ratios equal the
paper's exact prediction rule. Only the generic published compiler input remains. -/
theorem actualPredictor_polytime (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun,
      (∀ k : M.tm.K, Finite (M.tm.Γ k)) ∧
      (∀ x : List Bool, 0<x.length → 0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀ x : List Bool, (((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ) /
        ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=Paper37.Prediction.predict x.length x) :=
  ⟨sourceTMPoly simulation,(sourceMachine simulation).finiteAlphabets,
    sourceRun_denominator_pos,sourceRun_exact⟩

/-- Reusable machine transport for any fixed source-word AST. Resource
premises describe that AST's independently proved work and dynamic peak;
the encoding and all actual finite-TM obligations are discharged here. -/
def wordProgramTMPoly (simulation : BoundedLoopSimulationPrinciple)
    (e : Expr) (A a r C d s : ℕ)
    (hw : ∀ x : List Bool, e.work (inputEnv (sourceInputs x))≤A*(x.length+r)^a)
    (hp : ∀ x : List Bool, e.peak (inputEnv (sourceInputs x))≤C*(x.length+s)^d) :
    Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding
      (fun x => runProgram e (sourceInputs x)) := by
  let c:=compiler simulation e
  exact {
    toTM2ComputableAux := c.toTM2ComputableAux
    time := timePolynomial c.constant (Polynomial.C A*(Polynomial.X+Polynomial.C r)^a) Polynomial.X
      (Polynomial.C C*(Polynomial.X+Polynomial.C s)^d)
    outputsFun := by
      intro x
      apply outputsInTime_mono (c.outputs (sourceInputs x))
      rw [timePolynomial_eval]
      simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,Polynomial.eval_X]
      apply Nat.mul_le_mul_left
      apply executionBudget_le
      · exact (hw x).trans (Nat.mul_le_mul_left A
          (Nat.pow_le_pow_left (Nat.add_le_add_right (sourceLength_le_encoding x) r) a))
      · exact le_refl _
      · exact (hp x).trans (Nat.mul_le_mul_left C
          (Nat.pow_le_pow_left (Nat.add_le_add_right (sourceLength_le_encoding x) s) d)) }

theorem wordProgram_poly_exists (simulation : BoundedLoopSimulationPrinciple)
    (e : Expr) (A a r C d s : ℕ)
    (hw : ∀ x : List Bool, e.work (inputEnv (sourceInputs x))≤A*(x.length+r)^a)
    (hp : ∀ x : List Bool, e.peak (inputEnv (sourceInputs x))≤C*(x.length+s)^d) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding
      (fun x => runProgram e (sourceInputs x)), ∀ k : M.tm.K, Finite (M.tm.Γ k) :=
  ⟨wordProgramTMPoly simulation e A a r C d s hw hp,(compiler simulation e).finiteAlphabets⟩

end
end Paper37.UniformPredictionMachine
