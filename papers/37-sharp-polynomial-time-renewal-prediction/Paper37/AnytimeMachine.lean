import Paper37.AnytimeProgramPeak
import Paper37.UniformPredictionMachine

/-! The actual finite dyadic restart program on its concrete binary source
encoding, with a uniform finite-alphabet polynomial-time TM realization. -/
namespace Paper37.AnytimeMachine
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.UniformPredictionMachine Paper37.WordProgram Paper37.AnytimePrediction

def sourceRun (x : List Bool) : Value := runProgram Paper37.AnytimeProgram.program (sourceInputs x)

theorem sourceRun_eq_pair (x : List Bool) :
    sourceRun x=pairValue (Paper37.IntegerPredictor.conditionalPair
      (epochLength (epochIndex x.length)) (x.drop (epochStart (epochIndex x.length)))) :=
  Paper37.AnytimeProgram.program_eval _ x (sourceInputs_word x)

theorem sourceRun_denominator_pos (x : List Bool) :
    0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal := by
  rw [sourceRun_eq_pair]
  change 0<(Paper37.IntegerPredictor.conditionalPair _ _).2
  exact Paper37.IntegerPredictor.conditionalPair_denominator_pos _ _ (within_epoch_prefix_lt x)

/-- Exact identification with the actual horizon-free kernel G.1. -/
theorem sourceRun_true (x : List Bool) :
    (((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℝ)/
      ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=onlineKernel x true := by
  simpa only [sourceRun,runProgram,Rat.cast_natCast] using
    Paper37.AnytimeProgram.program_source_real _ x (sourceInputs_word x)

lemma source_work (x : List Bool) :
    Paper37.AnytimeProgram.program.work (inputEnv (sourceInputs x))≤3000*(x.length+2)^4 :=
  Paper37.AnytimeProgram.program_work _ x (sourceInputs_word x)

lemma source_peak (x : List Bool) :
    Paper37.AnytimeProgram.program.peak (inputEnv (sourceInputs x))≤
      10000000000000*(x.length+3)^12 :=
  Paper37.AnytimeProgram.program_peak _ x (sourceInputs_word x)

/-- One fixed TM computes every dyadic restart prediction. Its only external
premise is the generic simulation principle for all finite bounded-loop ASTs;
all source-specific program, operation and intermediate-bit bounds are proved. -/
def sourceTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun :=
  wordProgramTMPoly simulation Paper37.AnytimeProgram.program 3000 4 2 10000000000000 12 3
    source_work source_peak

theorem sourceTM_exists (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun,
      (∀k : M.tm.K,Finite (M.tm.Γ k)) ∧
      (∀x,0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀x,(((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℝ)/
        ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=onlineKernel x true) :=
  ⟨sourceTMPoly simulation,(compiler simulation Paper37.AnytimeProgram.program).finiteAlphabets,
    sourceRun_denominator_pos,sourceRun_true⟩

/-- The native arithmetic schedule through time N runs the actual same source
algorithm on each observed prefix and has the Appendix G fifth-degree bound. -/
theorem cumulative_arithmetic (x : List Bool) (N : ℕ) :
    (∑t∈Finset.range N,Paper37.AnytimeProgram.program.work
      (inputEnv (sourceInputs (x.take t))))≤3000*(N+1)^5 :=
  Paper37.AnytimeProgram.cumulativeWork_le x N

end
end Paper37.AnytimeMachine
