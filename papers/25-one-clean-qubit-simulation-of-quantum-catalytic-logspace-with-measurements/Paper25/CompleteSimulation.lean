import Paper25.TargetUniformAssembly
import Paper25.SourceTermUniformGenerated
import Paper25.SourceHistoryUniformCompilation
import Paper25.SimulatorFamilies

/-! The complete native, deterministic-logspace-uniform source-to-target
simulation. External published inputs and the original gate convention are
explicit. Every P25-specific component and its generator is constructed. -/
noncomputable section
namespace Paper25.CompleteSimulation
open OperationalModel OperationalModel.LocalCompilation OperationalModel.UniformCompilation
variable {G : EffectiveGateSet}

/-- One fixed finite transducer emits the actual complete target list, for
every binary input. There is no assumed whole-source-term, history, walk,
filter, preparation, reflection or simulator generation premise. -/
theorem target_logspace (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (external : ClassicalSimulationInputs G) (primitive : PrimitiveDescriptionConvention conv)
    (F : EffectiveSourceFamily G) :
    LogspaceGenerates (fun x => (SimulatorCircuit.target conv E (F.circuit x)).encode) := by
  have hd := source_duration_computes external.lists external.queries external.source
    external.sourceOperations F
  have P := SimulatorParameterUniform.parameters_generated external.lists external.arithmetic F
    (source_work_generated external.lists external.source F) hd
  have hw := SourceHistoryUniformCompilation.source_nativeWalk_generated conv E external primitive F P
  exact target_logspace_of_walk conv E external primitive F hd hw

/-- The constructed family retains the actual target circuit exactly. -/
def targetFamily (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (external : ClassicalSimulationInputs G) (primitive : PrimitiveDescriptionConvention conv)
    (F : EffectiveSourceFamily G) : EffectiveTargetFamily G :=
  SimulatorCircuit.family conv E F (target_logspace conv E external primitive F)

@[simp] theorem targetFamily_circuit (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (external : ClassicalSimulationInputs G) (primitive : PrimitiveDescriptionConvention conv)
    (F : EffectiveSourceFamily G) (x : Input) :
    (targetFamily conv E external primitive F).circuit x = SimulatorCircuit.target conv E (F.circuit x) := rfl

/-- Theorem 1, including actual local gates, one clean probe, polynomial
resources, deterministic-logspace uniformity and inverse-polynomial signed
Born bias. No P25 implementation or correctness conclusion is an input. -/
theorem theorem1 (spectral : UnitarySpectralTheorem)
    (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (fourier : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (classical : ClassicalSimulationInputs G) (primitive : PrimitiveDescriptionConvention conv)
    (F : EffectiveSourceFamily G) (language : Input → Bool)
    (hdecides : EffectiveSourceDecidesBoundedError F language) :
    ∃ Q : EffectiveTargetFamily G,
      (∀ x, Q.circuit x = SimulatorCircuit.target conv E (F.circuit x)) ∧
      EffectiveDecidesWithInversePolynomialBias Q language := by
  refine ⟨targetFamily conv E classical primitive F,fun _ => rfl,?_⟩
  exact SimulatorCircuit.family_decides spectral conv E fourier F language hdecides
    (target_logspace conv E classical primitive F)

theorem theorem1_exact (spectral : UnitarySpectralTheorem)
    (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (fourier : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (classical : ClassicalSimulationInputs G) (primitive : PrimitiveDescriptionConvention conv)
    (F : EffectiveSourceFamily G) (language : Input → Bool)
    (hdecides : EffectiveSourceDecidesExact F language) :
    ∃ Q : EffectiveTargetFamily G,
      (∀ x, Q.circuit x = SimulatorCircuit.target conv E (F.circuit x)) ∧
      EffectiveDecidesWithInversePolynomialBias Q language :=
  theorem1 spectral conv E fourier classical primitive F language hdecides.boundedError

/-- Languages decided by the actual source/target family semantics, with the
complete-input resource and uniformity fields retained in each witness. -/
def BQCL (G : EffectiveGateSet) : Set (Input → Bool) :=
  {language | ∃ F : EffectiveSourceFamily G, EffectiveSourceDecidesBoundedError F language}

def QCL (G : EffectiveGateSet) : Set (Input → Bool) :=
  {language | ∃ F : EffectiveSourceFamily G, EffectiveSourceDecidesExact F language}

def DQC1 (G : EffectiveGateSet) : Set (Input → Bool) :=
  {language | ∃ Q : EffectiveTargetFamily G, EffectiveDecidesWithInversePolynomialBias Q language}

theorem BQCL_subset_DQC1 (spectral : UnitarySpectralTheorem)
    (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (fourier : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (classical : ClassicalSimulationInputs G) (primitive : PrimitiveDescriptionConvention conv) :
    BQCL G ⊆ DQC1 G := by
  rintro language ⟨F,hdecides⟩
  obtain ⟨Q,_,hQ⟩ := theorem1 spectral conv E fourier classical primitive F language hdecides
  exact ⟨Q,hQ⟩

theorem QCL_subset_DQC1 (spectral : UnitarySpectralTheorem)
    (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (fourier : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (classical : ClassicalSimulationInputs G) (primitive : PrimitiveDescriptionConvention conv) :
    QCL G ⊆ DQC1 G := by
  rintro language ⟨F,hdecides⟩
  obtain ⟨Q,_,hQ⟩ := theorem1_exact spectral conv E fourier classical primitive F language hdecides
  exact ⟨Q,hQ⟩

end Paper25.CompleteSimulation
