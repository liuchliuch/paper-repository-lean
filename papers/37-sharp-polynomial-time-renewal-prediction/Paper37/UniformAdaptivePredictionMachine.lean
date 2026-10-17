import Paper37.UniformPredictionMachine
import Paper37.AdaptiveQueryPeak
import Paper37.AdaptiveQueryWork

/-! One fixed finite Turing machine computes the exact source adaptive
predictor, conditional only on the generic bounded-loop simulation theorem. -/
namespace Paper37.UniformAdaptivePredictionMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.WordProgram Paper37.AdaptiveQueryProgram
open Paper37.UniformPredictionMachine (sourceInputs sourceEncoding sourceInputs_word
  sourceLength_le_encoding sourceEncoding_length)

/-- The same concrete binary word encoding is used by both source predictors.
The adaptive horizon is computed by its fixed syntax from word slot40. -/
def sourceRun (x:List Bool) : Value := runProgram predictorProgram (sourceInputs x)

lemma sourceRun_eq_pair (x:List Bool) :
    sourceRun x=pairValue (Paper37.AdaptiveIntegerOutput.predictorPair x.length x) :=
  predictorProgram_eval _ x (sourceInputs_word x)

/-- The actual finite program returns a pair denoting the paper's adaptive
suffix average, with no support, tail, period or moment parameter as input. -/
theorem sourceRun_exact (x:List Bool) :
    (((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
      ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=
        Paper37.Adaptive.adaptivePredict x.length x :=
  predictorProgram_source _ x (sourceInputs_word x)

theorem sourceRun_denominator_pos (x:List Bool) (hx:0<x.length) :
    0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal := by
  rw [sourceRun_eq_pair]
  change 0<(Paper37.AdaptiveIntegerOutput.predictorPair x.length x).2
  change 0<(Paper37.IntegerOutput.pairSum
    (Paper37.AdaptiveIntegerOutput.suffixPairs x.length x)).2*x.length
  apply Nat.mul_pos _ hx
  apply Paper37.IntegerOutput.pairSum_denominator_pos
  intro p hp
  obtain ⟨t,rfl⟩:=List.mem_ofFn.mp hp
  apply Paper37.AdaptiveIntegerOutput.conditionalPair_denominator_pos
  simp only [List.length_drop]
  omega

lemma source_work (x:List Bool) :
    predictorProgram.work (inputEnv (sourceInputs x))≤6000*(x.length+2)^6 :=
  Paper37.AdaptiveQueryProgram.predictorProgram_work _ x (sourceInputs_word x)

lemma source_peak (x:List Bool) :
    predictorProgram.peak (inputEnv (sourceInputs x))≤10^30*(x.length+2)^21 :=
  Paper37.AdaptiveQueryPeak.predictorProgram_peak _ x (sourceInputs_word x)

/-- The actual compiled finite machine receives the single observed word and
returns the exact unreduced integer pair. No predictor-specific compiler or
polynomial-time assumption is supplied here. -/
def sourceTMPoly (simulation:BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun :=
  Paper37.UniformPredictionMachine.wordProgramTMPoly simulation predictorProgram
    6000 6 2 (10^30) 21 2 source_work source_peak

def sourceMachine (simulation:BoundedLoopSimulationPrinciple) : Compilation predictorProgram :=
  compiler simulation predictorProgram

/-- The external premise is the generic all-programs/all-inputs simulation
principle; every source-specific value, work, size and encoding fact is closed. -/
theorem sourceTM_exists (simulation:BoundedLoopSimulationPrinciple) :
    ∃ M:Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun,
      ∀k:M.tm.K,Finite (M.tm.Γ k) :=
  ⟨sourceTMPoly simulation,(sourceMachine simulation).finiteAlphabets⟩

/-- Execution of the same machine on the fully specified binary source input. -/
def sourceMachine_outputs (simulation:BoundedLoopSimulationPrinciple) (x:List Bool) :
    Turing.TM2OutputsInTime (sourceMachine simulation).tm
      (List.map (sourceMachine simulation).inputAlphabet.invFun (sourceEncoding.encode x))
      (some (List.map (sourceMachine simulation).outputAlphabet.invFun
        (valueEncoding.encode (sourceRun x))))
      ((sourceMachine simulation).constant*executionBudget predictorProgram (sourceInputs x)) :=
  (sourceMachine simulation).outputs (sourceInputs x)

/-- The concrete program and its exact output simultaneously satisfy the
source work and intermediate representation bounds for every observed word. -/
theorem source_algorithm_certificate (x:List Bool) :
    sourceRun x=pairValue (Paper37.AdaptiveIntegerOutput.predictorPair x.length x) ∧
      predictorProgram.work (inputEnv (sourceInputs x))≤6000*(x.length+2)^6 ∧
      predictorProgram.peak (inputEnv (sourceInputs x))≤10^30*(x.length+2)^21 :=
  ⟨sourceRun_eq_pair x,source_work x,source_peak x⟩

end
end Paper37.UniformAdaptivePredictionMachine
