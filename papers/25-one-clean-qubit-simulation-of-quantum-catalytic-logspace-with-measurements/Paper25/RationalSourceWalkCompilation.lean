import Paper25.SourceWalkCompilation
import Paper25.SelectorArithmetic

/-! Instantiation of the actual source walk with the represented numerical
weighted selector. No exact irrational selector gate is assumed. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper25.SourceWalkCompilation
open OperationalModel OperationalModel.LocalCompilation

/-- A complete actual source walk, parameterized only by the requested
one-qubit numerical precision. The resulting list has no preparation leaf. -/
def rationalCircuit {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (S : EffectiveSourceComputation G) (ell n : ℕ) :
    EffectiveCircuit G ((4+(ell+SourceHistoryCompilation.DataQubits S))+1) :=
  circuit conv S ell (conv.rotationRep (selectorAngle E n))

theorem rationalCircuit_error {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (S : EffectiveSourceComputation G) (ell n : ℕ)
    (τ : ℝ) (hprecision : bitError n ≤ τ/6) :
    ‖(rationalCircuit conv E S ell n).matrix - idealWalk S ell‖ ≤ 2*τ :=
  circuit_error conv S ell _ τ (selectorGate_error conv E n τ hprecision)

theorem rationalCircuit_error_bits {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (S : EffectiveSourceComputation G) (ell n : ℕ) :
    ‖(rationalCircuit conv E S ell n).matrix - idealWalk S ell‖ ≤ 12*bitError n := by
  have h := rationalCircuit_error conv E S ell n (6*bitError n) (by linarith)
  calc
    _ ≤ 2*(6*bitError n) := h
    _ = 12*bitError n := by ring

theorem rationalCircuit_length {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (S : EffectiveSourceComputation G) (ell n : ℕ) :
    (rationalCircuit conv E S ell n).length ≤
      3*conv.X.length + (conv.bound^2+conv.bound)*encoderGateBound conv ell conv.bound +
        16*conv.bound^5*(4*(conv.X.length+conv.bound)) := by
  apply (circuit_length conv S ell _).trans
  have hp : encoderGateBound conv ell (conv.rotationRep (selectorAngle E n)).length ≤
      encoderGateBound conv ell conv.bound := by
    exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (conv.rotationRep_length _)) _
  exact Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_left _ hp) _) _

end Paper25.SourceWalkCompilation
