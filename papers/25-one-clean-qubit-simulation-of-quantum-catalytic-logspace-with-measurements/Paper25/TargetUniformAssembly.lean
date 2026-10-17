import Paper25.FilterUniformCompilation
import Paper25.PlacementUniformCompilation
import Paper25.SimulatorExternalInputs

/-! Final composition of the independently generated native components. The
source-walk certificate is a component premise here; the final source-uniform
construction discharges it before the main theorem is stated. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000

lemma dataCircuit_generated (classical : FLListClosure) (grammar : InstructionDescriptionClosure)
    (arithmetic : NatArithmeticDescription)
    {G : EffectiveGateSet} {α : Type} {q : α → ℕ} (encode : α → Input)
    (C : ∀ a, EffectiveCircuit G (q a)) (hC : GeneratedCircuit encode C)
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hpoly : PolynomialBoundOn encode q) :
    GeneratedCircuit encode (fun a => dataCircuit (C a)) := by
  have hp : LogspaceComputes encode (fun a => (placementOfEmbedding (dataWires (q a))).encode) := by
    apply placement_generated classical arithmetic encode _
      (nat_add classical arithmetic encode q (fun _ => 1) hq (nat_const classical encode 1))
      hq hpoly
    have hi := indexed_counter_generated classical encode q
    have hpos := nat_add classical arithmetic (indexedInput encode q)
      (fun r => r.2.val) (fun _ => 1) hi (nat_const classical _ 1)
    simpa only [active_placementOfEmbedding_eq,dataWires,Fin.val_succ] using hpos
  exact embedCircuit_generated classical grammar encode _ C hp hC

lemma source_filter_width_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {G : EffectiveGateSet} (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G)
    (P : SimulatorParameterUniform.ParameterComputations F) :
    LogspaceComputes id (fun x => encodeNat (SourcePreparationPlacement.filterQubits (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x)) (FullPrecisionBudget.sourcePhase (F.circuit x)))) := by
  have hw := FilterUniformCompilation.source_walk_width_generated classical arithmetic parsing F P
  have hr := nat_add classical arithmetic id (fun _ => 1) _ (nat_const classical id 1) hw
  exact nat_add classical arithmetic id _ _ P.m hr

lemma source_filter_width_polynomial {G : EffectiveGateSet} (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => SourcePreparationPlacement.filterQubits (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x)) (FullPrecisionBudget.sourcePhase (F.circuit x))) := by
  apply (SourceCircuitSimulation.mixed_resources F).1.mono
  intro x
  have he := FullReflectionPlacement.filterQubits_eq (F.circuit x)
    (SourceCircuitSimulation.clockBits (F.circuit x)) (FullPrecisionBudget.sourcePhase (F.circuit x))
  rw [he]
  have hs := SourceCircuitSimulation.physical_small_qubits (F.circuit x)
  change _ ≤ simulatorMixedQubits (F.circuit x).workQubits (F.circuit x).catalystQubits
    (SourceCoordinates.duration (F.circuit x))
  simp only [FullPrecisionBudget.sourcePhase]
  rw [hs]
  unfold simulatorMixedQubits
  omega

/-- Actual complete target bytes from the source-duration and source-walk
components. All remaining pure parameter and physical-position queries are
derived here; none is an additional paper-specific external assumption. -/
theorem target_logspace_of_walk {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (external : Paper25.ClassicalSimulationInputs G)
    (primitive : PrimitiveDescriptionConvention conv) (F : EffectiveSourceFamily G)
    (hDuration : SimulatorParameterUniform.UnaryComputes (fun x => SourceCoordinates.duration (F.circuit x)))
    (hwalk : GeneratedCircuit id (fun x => FullFilterPlacement.nativeWalk conv (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x))
      (conv.rotationRep (selectorAngle E (FullPrecisionBudget.sourcePrecision (F.circuit x)))))) :
    LogspaceGenerates (fun x => (SimulatorCircuit.target conv E (F.circuit x)).encode) := by
  have P := SimulatorParameterUniform.parameters_generated external.lists external.arithmetic F
    (source_work_generated external.lists external.source F) hDuration
  have hUF := FilterUniformCompilation.source_nativeUF_generated conv E external.lists external.rational
    external.instructions primitive external.binary external.shift external.arithmetic external.fourier
    external.recipes external.source F P hwalk
  have hF := source_preparation_generated external.lists external.instructions external.arithmetic
    external.binary external.source conv F hDuration
  have hR := source_reflection_generated external.lists external.instructions primitive
    external.arithmetic external.source F hDuration
  have hW : GeneratedCircuit id (fun x => SimulatorCircuit.readoutW conv E (F.circuit x)) :=
    append_generated external.lists id _ _ hUF
      (adjointCircuit_generated external.lists primitive id _ hF)
  have hq := source_filter_width_generated external.lists external.arithmetic external.source F P
  have hdata := dataCircuit_generated external.lists external.instructions external.arithmetic id
    (fun x => SimulatorCircuit.readoutW conv E (F.circuit x)) hW hq (source_filter_width_polynomial F)
  have hcontrolled := controlledCircuit_generated external.lists primitive id
    (fun x => SimulatorCircuit.reflection conv (F.circuit x)) hR
  have hV := append_generated external.lists id _ _ hdata hcontrolled
  have hwidth := nat_add external.lists external.arithmetic id _ (fun _ => 1) hq
    (nat_const external.lists id 1)
  exact readoutCircuit_logspace external.lists external.instructions primitive id _ hV hwidth

end Paper25.OperationalModel.UniformCompilation
