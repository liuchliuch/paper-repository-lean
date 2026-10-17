import Paper37.FullBlockProgramWork
import Paper37.FullBlockProgramPeak

/-! The requested full-block probability is computed by a single actual
finite polynomial-time binary Turing machine. The only external input is the
generic simulation theorem for every finite bounded-loop program. -/
namespace Paper37.FullBlockProgram
noncomputable section
open Paper37.BoundedLoop Paper37.BoundedLoopEncoding Paper37.BoundedLoopMachine
open Paper37.UniformPredictionMachine (sourceInputs sourceInputs_word sourceEncoding wordProgramTMPoly)
open Paper37.WordProgram

def sourceRun (x : List Bool) : Value := runProgram program (sourceInputs x)

lemma sourceRun_eq_pair (x : List Bool) : sourceRun x=pairValue (blockPair x) :=
  program_eval _ x (sourceInputs_word x)

/-- Full source probability, including the ordinary Z normalizer and the
uniform first-renewal mixture, on every binary block including the empty one. -/
theorem sourceRun_exact (x : List Bool) :
    (((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
      ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=
        Paper37.Prediction.blockAssignment x := by
  rw [sourceRun_eq_pair]
  exact blockPair_exact x

theorem sourceRun_denominator_pos (x : List Bool) :
    0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal := by
  rw [sourceRun_eq_pair]
  exact blockPair_denominator_pos x

/-- The very rational value emitted by this machine satisfies the source
pointwise regret bound, for every positive word of every finite-mean law. -/
theorem source_log_regret (μ : Paper37.Renewal.Law) (x : List Bool)
    (hp : 0<Paper37.Renewal.blockMass μ x) :
    let q : ℚ := (((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
      ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal
    Real.log (Paper37.Renewal.blockMass μ x / (q:ℝ))≤
      Paper37.AnalyticBounds.redundancyBound x.length := by
  dsimp only
  rw [sourceRun_exact]
  exact Paper37.RateUpper.pointwise_block_regret μ x hp

lemma source_work (x : List Bool) :
    program.work (inputEnv (sourceInputs x))≤3000*(x.length+2)^4 :=
  program_work _ x (sourceInputs_word x)

lemma source_peak (x : List Bool) :
    program.peak (inputEnv (sourceInputs x))≤1000000000000000*(x.length+3)^12 :=
  program_peak _ x (sourceInputs_word x)

def sourceTMPoly (simulation : BoundedLoopSimulationPrinciple) :
    Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun :=
  wordProgramTMPoly simulation program 3000 4 2 1000000000000000 12 3 source_work source_peak

/-- C.4 for the source full-block assignment: one uniform finite TM outputs
a valid exact rational encoding for every requested block Q_N(x), with
polynomial time in the length of the actual binary input encoding. -/
theorem actualBlockAssignment_polytime (simulation : BoundedLoopSimulationPrinciple) :
    ∃ M : Turing.TM2ComputableInPolyTime sourceEncoding valueEncoding sourceRun,
      (∀ k : M.tm.K,Finite (M.tm.Γ k)) ∧
      (∀ x : List Bool,0<((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal) ∧
      (∀ x : List Bool,(((sourceRun x).arrayVal[0]?.getD (Value.nat 0)).natVal:ℚ)/
        ((sourceRun x).arrayVal[1]?.getD (Value.nat 0)).natVal=Paper37.Prediction.blockAssignment x) :=
  ⟨sourceTMPoly simulation,(compiler simulation program).finiteAlphabets,
    sourceRun_denominator_pos,sourceRun_exact⟩

/-- The actual program, source-specific exact semantics and both execution
resource bounds are proved together; no resource premise is supplied. -/
theorem source_algorithm_certificate (x : List Bool) :
    sourceRun x=pairValue (blockPair x) ∧
      program.work (inputEnv (sourceInputs x))≤3000*(x.length+2)^4 ∧
      program.peak (inputEnv (sourceInputs x))≤1000000000000000*(x.length+3)^12 :=
  ⟨sourceRun_eq_pair x,source_work x,source_peak x⟩

end
end Paper37.FullBlockProgram
