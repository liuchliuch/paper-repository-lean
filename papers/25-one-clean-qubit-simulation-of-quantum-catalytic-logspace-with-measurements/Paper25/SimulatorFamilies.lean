import Paper25.SimulatorCorrectness
import Paper25.FullCompilationResources

/-! Package the fixed native circuit after its concrete description generator
has been proved. The complete uniformity theorem supplies that proof in the
final assembly; this lower packaging lemma does not assert its existence. -/
noncomputable section
namespace Paper25.SimulatorCircuit
open OperationalModel OperationalModel.LocalCompilation
variable {G : EffectiveGateSet}

def family (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (F : EffectiveSourceFamily G)
    (hgenerated : LogspaceGenerates (fun x => (target conv E (F.circuit x)).encode)) :
    EffectiveTargetFamily G where
  circuit x := target conv E (F.circuit x)
  uniform := hgenerated
  mixed_polynomial := by
    simpa only [target_mixed_qubits] using (SourceCircuitSimulation.mixed_resources F).1
  gates_polynomial := FullCompilationResources.simulator_target_gatePolynomial conv E F

@[simp] lemma family_circuit (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (F : EffectiveSourceFamily G) (hgenerated) (x : Input) :
    (family conv E F hgenerated).circuit x = target conv E (F.circuit x) := rfl

/-- The signed bias is computed from the constructed target's own density
semantics. No acceptance probability is supplied independently. -/
theorem family_decides (external : UnitarySpectralTheorem)
    (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (F : EffectiveSourceFamily G) (language : Input → Bool)
    (hdecides : EffectiveSourceDecidesBoundedError F language)
    (hgenerated : LogspaceGenerates (fun x => (target conv E (F.circuit x)).encode)) :
    EffectiveDecidesWithInversePolynomialBias (family conv E F hgenerated) language := by
  apply SourceCircuitSimulation.target_family_decides_of_error external F language hdecides
  intro x
  exact accept_error conv E standard (F.circuit x)
    (SourceCircuitSimulation.spectralData external (F.circuit x))

end Paper25.SimulatorCircuit
