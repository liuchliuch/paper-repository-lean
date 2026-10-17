import Paper25.ClassicalInterfaceTransport
import Paper25.BinaryDataCompilation
import Paper25.NatVectorParsing

/-! The complete classical external input ledger, as a record of generic
string/arithmetic/grammar facts. No field mentions a P25 circuit, target
probability, source expansion, history, walk, filter or whole compiler. -/
noncomputable section
namespace Paper25
open OperationalModel OperationalModel.UniformCompilation

structure ClassicalSimulationInputs (G : EffectiveGateSet) : Prop where
  lists : FLListClosure
  instructions : InstructionDescriptionClosure
  arithmetic : NatArithmeticDescription
  unaryPrefix : UnaryPrefixParsing
  queries : FLDataQueryDescription
  source : SourceDescriptionParsing G
  sourceOperations : SourceOperationParsing G
  binary : BinaryDataDescription
  vectors : NatVectorParsing
  shift : BinaryShiftDescription
  rational : ClassicalDescriptionClosure
  recipes : RecipeDescriptionClosure

def ClassicalSimulationInputs.fourier {G : EffectiveGateSet}
    (external : ClassicalSimulationInputs G) : OperationalModel.FourierCompilation.UnaryCounterArithmetic :=
  fourierArithmetic external.lists external.arithmetic external.unaryPrefix

end Paper25
