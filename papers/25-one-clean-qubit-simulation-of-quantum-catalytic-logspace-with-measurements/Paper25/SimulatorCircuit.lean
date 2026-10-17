import Paper25.FullFilterPlacement
import Paper25.FullReflectionPlacement
import Paper25.FullPrecisionBudget

/-! The single explicit source-to-target circuit. The spectral theorem is
proof data only and is absent from every generated gate and raw payload. -/
noncomputable section
namespace Paper25.SimulatorCircuit
open OperationalModel OperationalModel.LocalCompilation
open FullPrecisionBudget SourceCoordinates SourceSimulation SourcePreparationPlacement SourceTermCompilation
variable {G : EffectiveGateSet}

def filter (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (C : EffectiveSourceComputation G) :
    EffectiveCircuit G (filterQubits C (SourceCircuitSimulation.clockBits C) (sourcePhase C)) :=
  FullFilterPlacement.nativeUF conv E C (SourceCircuitSimulation.clockBits C) (sourcePhase C)
    (sourcePrecision C) (sourcePrecision C) (sourcePrecision C) (sourcePrecision C)

def preparation (conv : GateConvention G) (C : EffectiveSourceComputation G) :
    EffectiveCircuit G (filterQubits C (SourceCircuitSimulation.clockBits C) (sourcePhase C)) :=
  placedF conv C (SourceCircuitSimulation.clockBits C) (sourcePhase C)
    (terminalClock (SourceCircuitSimulation.clockBits C) (duration C)
      (SourceCircuitSimulation.clock_valid C))

/-- Chronological UF then F dagger implements F dagger UF. -/
def readoutW (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (C : EffectiveSourceComputation G) :
    EffectiveCircuit G (filterQubits C (SourceCircuitSimulation.clockBits C) (sourcePhase C)) :=
  filter conv E C ++ adjointCircuit conv (preparation conv C)

def reflection (conv : GateConvention G) (C : EffectiveSourceComputation G) :
    EffectiveCircuit G (filterQubits C (SourceCircuitSimulation.clockBits C) (sourcePhase C)) :=
  FullReflectionPlacement.reflection conv C (SourceCircuitSimulation.clockBits C) (sourcePhase C)

/-- One clean probe, a mixed trace-cancellation bit and the entire mixed
filter register; the final probe Born measurement is the only measurement. -/
def target (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (C : EffectiveSourceComputation G) : EffectiveTargetCircuit G :=
  readoutCircuit conv (traceCancellationCircuit conv (readoutW conv E C) (reflection conv C))

lemma phaseBits_eq (C : EffectiveSourceComputation G) : sourcePhase C =
    phaseBits (clockSize (duration C)) (2^C.workQubits) := by
  unfold sourcePhase SelectedFilter.sourcePhaseBits SourceCircuitSimulation.clockBits
  rw [SimulationParameters.clock_card,SimulationParameters.work_card,restQubits_add_one]

/-- The actual number of mixed physical qubits is the stated resource bound. -/
theorem target_mixed_qubits (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (C : EffectiveSourceComputation G) :
    (target conv E C).mixedQubits =
      simulatorMixedQubits C.workQubits C.catalystQubits (duration C) := by
  change filterQubits C (SourceCircuitSimulation.clockBits C) (sourcePhase C)+1 = _
  unfold filterQubits walkQubits encoderQubits sourceQubits
    simulatorMixedQubits simulatorSmallQubits
  rw [phaseBits_eq]
  unfold SourceCircuitSimulation.clockBits SimulationParameters.clockBits
  omega

end Paper25.SimulatorCircuit
