import Paper25.CompilationGateBounds
import Paper25.FullFilterPlacement
import Paper25.SimulatorCircuit

/-! Polynomial gate counts of the single explicitly constructed simulator,
from actual local gate lists and the source family's original resources. -/
noncomputable section
namespace Paper25.FullCompilationResources
open OperationalModel OperationalModel.LocalCompilation OperationalModel.CoherentCompilation
open SourceHistoryCompilation SourceWalkCompilation
variable {G : EffectiveGateSet}

lemma nativeUF_length (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (S : EffectiveSourceComputation G) (ell m precision selectorPrecision n k : ℕ) :
    (FullFilterPlacement.nativeUF conv E S ell m precision selectorPrecision n k).length ≤
      filterGateBound conv m (walkGateBound conv ell) := by
  apply (compiledFilter_length conv E precision m _ _ n k).trans
  apply filterGateBound_mono
  simpa only [FullFilterPlacement.nativeWalk,rewireCircuit_length,SourceWalkCompilation.rationalCircuit,
    walkGateBound] using rationalCircuit_length conv E S ell selectorPrecision

theorem nativeUF_gatePolynomial (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (S : Input → EffectiveSourceComputation G) (ell m precision selectorPrecision n k : Input → ℕ)
    (hEll : PolynomialBound (fun x => 2^ell x)) (hm : PolynomialBound (fun x => 2^m x)) :
    PolynomialBound (fun x =>
      (FullFilterPlacement.nativeUF conv E (S x) (ell x) (m x)
        (precision x) (selectorPrecision x) (n x) (k x)).length) :=
  (filterGateBound_polynomial conv hm (walkGateBound_polynomial conv hEll)).mono
    (fun x => nativeUF_length conv E (S x) (ell x) (m x) (precision x) (selectorPrecision x) (n x) (k x))

theorem source_nativeUF_gatePolynomial (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (F : EffectiveSourceFamily G) (precision selectorPrecision n k : Input → ℕ) :
    PolynomialBound (fun x => (FullFilterPlacement.nativeUF conv E (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x)) (FullPrecisionBudget.sourcePhase (F.circuit x))
      (precision x) (selectorPrecision x) (n x) (k x)).length) :=
  nativeUF_gatePolynomial conv E F.circuit _ _ precision selectorPrecision n k
    (sourceClock_dimension_polynomial F) (FullPrecisionBudget.sourcePhase_dimension_polynomial F)

lemma source_other_dimension_polynomial (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => 2^(FullReflectionPlacement.otherQubits (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x)) (FullPrecisionBudget.sourcePhase (F.circuit x)))) := by
  apply (SourceCircuitSimulation.mixed_resources F).2.mono
  intro x
  let S := F.circuit x
  have he : FullReflectionPlacement.otherQubits S (SourceCircuitSimulation.clockBits S)
      (FullPrecisionBudget.sourcePhase S)+1 = simulatorSmallQubits S.workQubits (SourceCoordinates.duration S) := by
    unfold FullReflectionPlacement.otherQubits
    simp only [SourceCoordinates.restQubits_add_one,SimulatorCircuit.phaseBits_eq]
    unfold simulatorSmallQubits SourceCircuitSimulation.clockBits SimulationParameters.clockBits
    omega
  rw [←he]
  exact Nat.pow_le_pow_right (by decide) (Nat.le_succ _)

lemma simulator_reflection_gatePolynomial (conv : GateConvention G) (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => (SimulatorCircuit.reflection conv (F.circuit x)).length) := by
  have h := (((control_overhead_polynomial (source_other_dimension_polynomial F) conv.bound).mul
    (PolynomialBound.const (5*conv.X.length+6*conv.bound))).add
      (PolynomialBound.const (4*(conv.X.length+conv.bound))))
  exact h.mono (fun x => FullReflectionPlacement.reflection_length conv _ _ _)

lemma simulator_preparation_gatePolynomial (conv : GateConvention G) (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => (SimulatorCircuit.preparation conv (F.circuit x)).length) := by
  exact placedF_gatePolynomial conv F _ _ _
    ((sourceClock_dimension_polynomial F).mono (fun x => Paper25.nat_le_two_pow _))

lemma simulator_filter_gatePolynomial (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => (SimulatorCircuit.filter conv E (F.circuit x)).length) :=
  source_nativeUF_gatePolynomial conv E F _ _ _ _

theorem simulator_target_gatePolynomial (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => (SimulatorCircuit.target conv E (F.circuit x)).gateCount) := by
  have hW : PolynomialBound (fun x => (SimulatorCircuit.readoutW conv E (F.circuit x)).length) := by
    apply ((simulator_filter_gatePolynomial conv E F).add
      ((PolynomialBound.const conv.bound).mul (simulator_preparation_gatePolynomial conv F))).mono
    intro x
    simp only [SimulatorCircuit.readoutW,List.length_append]
    exact Nat.add_le_add_left (adjointCircuit_length conv _) _
  have hC := (hW.add ((PolynomialBound.const conv.bound).mul
    (simulator_reflection_gatePolynomial conv F))).mono
      (fun x => traceCancellationCircuit_length conv _ _)
  exact ((PolynomialBound.const conv.bound).mul (hC.add (PolynomialBound.const 2))).mono
    (fun x => readoutCircuit_length conv _)

end Paper25.FullCompilationResources
