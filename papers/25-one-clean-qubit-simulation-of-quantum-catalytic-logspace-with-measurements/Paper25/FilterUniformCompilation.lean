import Paper25.FullFilterPlacement
import Paper25.UniformCompilation
import Paper25.BinaryDataCompilation
import Paper25.SimulatorParameterUniform

/-! Uniform generation of the actual native coherent filter. The generator
is assembled from the given source-walk component, the fixed QFT template,
actual raw numerical label angles, and the generic native gate transforms.
The query interface below contains strings and counters only, with no matrix,
filter description, or complete compiler premise. -/
noncomputable section
namespace Paper25.OperationalModel.FilterUniformCompilation
open LocalCompilation UniformCompilation CoherentCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1600000
set_option synthInstance.maxSize 512

abbrev LabelContext {α : Type} (encode : α → Input) (m : α → ℕ) :=
  elementContext encode (fun a => @List.ofFn Bit (m a))

/-- Pure parameter-query machines for the fixed filter template. The unary
phase count bounds every enumerated power; raw rationals retain their bytes. -/
structure ParameterQueries {α : Type} (encode : α → Input)
    (m q precision n k : α → ℕ) (δ : α → RationalRep) : Prop where
  phase : LogspaceComputes encode (fun a => encodeNat (m a))
  data : LogspaceComputes encode (fun a => encodeNat (q a))
  precision_query : LogspaceComputes encode (fun a => encodeNat (precision a))
  labels : LogspaceComputes encode (fun a => encodeNat (2^(m a)))
  labels_polynomial : PolynomialBoundOn encode (fun a => 2^(m a))
  delta : LogspaceComputes encode (fun a => (δ a).encode)
  labels_raw : LogspaceComputes encode (fun a => (RationalRep.ofRat (2^(m a) : ℕ)).encode)
  cosine_precision : LogspaceComputes encode (fun a => encodeNat (n a))
  arccos_precision : LogspaceComputes encode (fun a => encodeNat (k a))
  label_index : LogspaceComputes (LabelContext encode m)
    (fun p => encodeNat (SelectedFilter.bitsBinaryIndex (m p.1) p.2).val)
  label_index_raw : LogspaceComputes (LabelContext encode m)
    (fun p => (RationalRep.ofRat (SelectedFilter.bitsBinaryIndex (m p.1) p.2).val).encode)

lemma label_pullback (classical : FLListClosure) {α : Type}
    (encode : α → Input) (m : α → ℕ) (output : α → Input)
    (h : LogspaceComputes encode output) :
    LogspaceComputes (LabelContext encode m) (fun p => output p.1) :=
  classical.strings.compose (LabelContext encode m) encode Sigma.fst output
    (classical.strings.contextLeft _ _) h

lemma label_index_polynomial {α : Type} (encode : α → Input) (m : α → ℕ)
    (hM : PolynomialBoundOn encode (fun a => 2^(m a))) :
    PolynomialBoundOn (LabelContext encode m)
      (fun p => (SelectedFilter.bitsBinaryIndex (m p.1) p.2).val) := by
  obtain ⟨C,d,hM⟩ := hM
  refine ⟨C,d,fun p => (SelectedFilter.bitsBinaryIndex (m p.1) p.2).isLt.le.trans ((hM p.1).trans ?_)⟩
  have hl : (encode p.1).length+1 ≤ (LabelContext encode m p).length+1 := by
    simp only [LabelContext, elementContext, List.length_append]
    omega
  gcongr

lemma phase_width_polynomial {α : Type} (encode : α → Input) (m : α → ℕ)
    (hM : PolynomialBoundOn encode (fun a => 2^(m a))) : PolynomialBoundOn encode m :=
  FourierCompilation.polynomial_counter_mono encode m _ (fun a => (Nat.lt_two_pow_self).le) hM

/-- Actual raw angle-output bytes, from the elementary numerical calls and
pure parameter queries, for every enumerated phase word. -/
theorem representedAngles_computes (E : ElementaryAnalyticInputs)
    (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    {α : Type} (encode : α → Input) (m q precision n k : α → ℕ) (δ : α → RationalRep)
    (Q : ParameterQueries encode m q precision n k δ) :
    LogspaceComputes (LabelContext encode m)
      (fun p => (representedAngles E (δ p.1) (m p.1) (n p.1) (k p.1) p.2).encode) := by
  exact representedLabelFilterAngle_computes E numeric (LabelContext encode m)
    (fun p => δ p.1) (fun p => RationalRep.ofRat (2^(m p.1):ℕ))
    (fun p => RationalRep.ofRat (SelectedFilter.bitsBinaryIndex (m p.1) p.2).val)
    (fun p => n p.1) (fun p => k p.1)
    (label_pullback classical encode m _ Q.delta) (label_pullback classical encode m _ Q.labels_raw)
    Q.label_index_raw (label_pullback classical encode m _ Q.cosine_precision)
    (label_pullback classical encode m _ Q.arccos_precision)

/-- The actual SELECT list is generated from the actual raw rotation outputs;
there is no assumed label-rotation or whole-filter generator. -/
theorem labelCircuit_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    {α : Type} (encode : α → Input) (m q precision n k : α → ℕ) (δ : α → RationalRep)
    (Q : ParameterQueries encode m q precision n k δ) :
    GeneratedCircuit encode (fun a => labelCircuit conv (m a) (q a)
      (representedAngles E (δ a) (m a) (n a) (k a))) := by
  let ctx := LabelContext encode m
  have hr := rotationRep_generated classical primitive ctx _
    (representedAngles_computes E classical numeric encode m q precision n k δ Q)
  have hbranch := tensorCircuit_generated classical grammar ctx
    (fun p => conv.rotationRep (representedAngles E (δ p.1) (m p.1) (n p.1) (k p.1) p.2))
    (fun p => ([] : EffectiveCircuit G (q p.1))) hr (nil_generated classical ctx _)
    (classical.strings.constant ctx (encodeNat 1)) (label_pullback classical encode m _ Q.data)
  exact selectCircuit_generated classical primitive encode _
    (classical.strings.concat encode _ _ Q.phase Q.labels) Q.labels hbranch

/-- The native QFT description is produced by the fixed nested-counter
network, then extended by the real rotation and data wires. -/
theorem fourier_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (shift : BinaryShiftDescription) (arithmetic : FourierCompilation.UnaryCounterArithmetic)
    (closure : RecipeDescriptionClosure)
    {α : Type} (encode : α → Input) (m q precision n k : α → ℕ) (δ : α → RationalRep)
    (Q : ParameterQueries encode m q precision n k δ) :
    GeneratedCircuit encode (fun a => FourierCompilation.circuitOnData conv E (precision a) (m a) (1+q a)) := by
  have hF := generated_of_logspace grammar encode (fun _ => 0) _
    (FourierCompilation.circuit_computes_standard conv E classical numeric grammar primitive shift
      arithmetic closure m precision encode (fun _ => 0) Q.phase Q.precision_query
      (numeric.constant encode (encodeNat 0)) (phase_width_polynomial encode m Q.labels_polynomial))
  have hdata : LogspaceComputes encode (fun a => encodeNat (1+q a)) :=
    FourierCompilation.unary_binary_computes numeric encode (fun _ => 1) q (·+·)
      (numeric.constant encode (encodeNat 1)) Q.data arithmetic.add
  exact tensorCircuit_generated classical grammar encode _ _ hF (nil_generated classical encode _)
    Q.phase hdata

/-- Complete native PE/filter generation from its independently generated walk
component. Every remaining hypothesis is a published elementary primitive or
pure classical data/query interface. -/
theorem compiledFilter_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (shift : BinaryShiftDescription) (arithmetic : FourierCompilation.UnaryCounterArithmetic)
    (closure : RecipeDescriptionClosure)
    {α : Type} (encode : α → Input) (m q precision n k : α → ℕ) (δ : α → RationalRep)
    (walk : ∀ a, EffectiveCircuit G (q a)) (Q : ParameterQueries encode m q precision n k δ)
    (hwalk : GeneratedCircuit encode walk) :
    GeneratedCircuit encode (fun a => compiledFilter conv E (precision a) (m a) (walk a) (δ a) (n a) (k a)) := by
  have hW := tensorCircuit_generated classical grammar encode
    (fun _ => ([] : EffectiveCircuit G 1)) walk (nil_generated classical encode _) hwalk
    (classical.strings.constant encode (encodeNat 1)) Q.data
  have hF := fourier_generated conv E classical numeric grammar primitive shift arithmetic closure
    encode m q precision n k δ Q
  have hPE := phaseEstimationCircuit_generated classical primitive encode
    (fun a j => (SelectedFilter.bitsBinaryIndex (m a) j).val)
    (fun a => rotationSpectator (walk a))
    (fun a => FourierCompilation.circuitOnData conv E (precision a) (m a) (1+q a))
    hW hF (classical.strings.concat encode _ _ Q.phase Q.labels) Q.labels
    Q.label_index (label_index_polynomial encode m Q.labels_polynomial)
  exact coherentFilterCircuit_generated classical primitive encode _ _ hPE
    (labelCircuit_generated conv E classical numeric grammar primitive encode m q precision n k δ Q)


/-- Binary word reading and raw-natural printing discharge both label queries
and the actual raw M bytes of the numerical filter algorithm. -/
theorem parameterQueries_of_data (classical : FLListClosure) (binary : BinaryDataDescription)
    {α : Type} (encode : α → Input) (m q precision n k : α → ℕ) (δ : α → RationalRep)
    (hm : LogspaceComputes encode (fun a => encodeNat (m a)))
    (hq : LogspaceComputes encode (fun a => encodeNat (q a)))
    (hp : LogspaceComputes encode (fun a => encodeNat (precision a)))
    (hM : LogspaceComputes encode (fun a => encodeNat (2^(m a))))
    (hMpoly : PolynomialBoundOn encode (fun a => 2^(m a)))
    (hδ : LogspaceComputes encode (fun a => (δ a).encode))
    (hn : LogspaceComputes encode (fun a => encodeNat (n a)))
    (hk : LogspaceComputes encode (fun a => encodeNat (k a))) :
    ParameterQueries encode m q precision n k δ := by
  let ctx := LabelContext encode m
  have hmc := label_pullback classical encode m _ hm
  have hMc := label_pullback classical encode m _ hM
  have hw : LogspaceComputes ctx (fun p => List.ofFn p.2) := classical.strings.contextRight _ _
  exact {
    phase := hm
    data := hq
    precision_query := hp
    labels := hM
    labels_polynomial := hMpoly
    delta := hδ
    labels_raw := by simpa only [rawNatRep_ofRat] using rawNat_generated classical binary encode _ hM
    cosine_precision := hn
    arccos_precision := hk
    label_index := word_value_generated classical binary ctx (fun p => p.2) hmc hMc hw
    label_index_raw := by
      simpa only [rawNatRep_ofRat] using word_rawNat_generated classical binary ctx (fun p => p.2) hmc hMc hw }

lemma reciprocal_raw_eq (d : ℕ) (hd : 0 < d) :
    (RationalRep.ofRat 1).div (rawNatRep d) = (⟨1,d,hd⟩ : RationalRep) := by
  have hn : (d:ℤ) ≠ 0 := by exact_mod_cast hd.ne'
  have hp : (0:ℤ) < d := by exact_mod_cast hd
  simp [RationalRep.div, RationalRep.ofIntFraction, RationalRep.ofRat, rawNatRep, hn, hp, hd, hd.ne']

/-- The exact unreduced numerator-one fraction is generated by raw arithmetic;
no canonical rational reduction or gcd algorithm is needed. -/
lemma reciprocal_generated (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (binary : BinaryDataDescription) {α : Type} (encode : α → Input)
    (d : α → ℕ) (hd : ∀ a, 0 < d a)
    (hden : LogspaceComputes encode (fun a => encodeNat (d a))) :
    LogspaceComputes encode (fun a => (⟨1,d a,hd a⟩ : RationalRep).encode) := by
  have h := computes_represented_binary numeric encode (fun _ => RationalRep.ofRat 1)
    (fun a => rawNatRep (d a)) RationalRep.div
    (numeric.constant encode ((RationalRep.ofRat 1).encode))
    (rawNat_generated classical binary encode d hden) numeric.rationalDiv
  simpa only [reciprocal_raw_eq _ (hd _)] using h

/-- Source-native UF generation, retaining only the independently generated
source-walk component as an intermediate compiler premise. -/
theorem nativeUF_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (shift : BinaryShiftDescription) (arithmetic : FourierCompilation.UnaryCounterArithmetic)
    (closure : RecipeDescriptionClosure)
    {α : Type} (encode : α → Input) (S : α → EffectiveSourceComputation G)
    (ell m precision selectorPrecision n k : α → ℕ)
    (Q : ParameterQueries encode m (fun a => SourcePreparationPlacement.walkQubits (S a) (ell a))
      precision n k (fun a => FullFilterPlacement.sourceDeltaRaw (S a) (ell a)))
    (hwalk : GeneratedCircuit encode (fun a => FullFilterPlacement.nativeWalk conv (S a) (ell a)
      (conv.rotationRep (selectorAngle E (selectorPrecision a))))) :
    GeneratedCircuit encode (fun a => FullFilterPlacement.nativeUF conv E (S a)
      (ell a) (m a) (precision a) (selectorPrecision a) (n a) (k a)) :=
  compiledFilter_generated conv E classical numeric grammar primitive shift arithmetic closure
    encode m _ precision n k _ _ Q hwalk


lemma source_walk_width_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    {G : EffectiveGateSet} (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G)
    (P : SimulatorParameterUniform.ParameterComputations F) :
    LogspaceComputes id (fun x => encodeNat (SourcePreparationPlacement.walkQubits (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x)))) := by
  have hs : LogspaceComputes id (fun x => encodeNat (SourceTermCompilation.sourceQubits (F.circuit x))) :=
    source_qubits_generated classical arithmetic parsing F
  have hd := nat_add classical arithmetic id _ _ hs hs
  have ht := nat_add classical arithmetic id _ _ P.ell hd
  have hb := nat_add classical arithmetic id _ _ (nat_const classical id 3) ht
  have he := nat_add classical arithmetic id _ _ (nat_const classical id 1) hb
  exact nat_add classical arithmetic id _ _ he (nat_const classical id 1)

lemma sourceDeltaRaw_eq_fraction {G : EffectiveGateSet} (S : EffectiveSourceComputation G) :
    FullFilterPlacement.sourceDeltaRaw S (SourceCircuitSimulation.clockBits S) =
      (⟨1,FullPrecisionBudget.sourceDeltaDen S,FullPrecisionBudget.sourceDeltaDen_pos S⟩ : RationalRep) := by
  change (⟨1,FullPrecisionBudget.deltaDen
    (Fintype.card (StatePreparation.Bits (SourceCircuitSimulation.clockBits S)))
    (Fintype.card (StatePreparation.WorkSpace (SourceCoordinates.restQubits S))),_⟩ : RationalRep) = _
  congr 1
  simp only [FullPrecisionBudget.sourceDeltaDen, FullPrecisionBudget.deltaDen,
    SourceCircuitSimulation.clockBits, SimulationParameters.clock_card,
    SimulationParameters.work_card, SourceCoordinates.restQubits_add_one]

/-- All filter parameter-query machines are constructed from the original
source parser and the already derived numerical parameter computations. -/
theorem source_parameterQueries (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (binary : BinaryDataDescription) (arithmetic : NatArithmeticDescription)
    {G : EffectiveGateSet} (parsing : SourceDescriptionParsing G) (F : EffectiveSourceFamily G)
    (P : SimulatorParameterUniform.ParameterComputations F) :
    ParameterQueries id (fun x => FullPrecisionBudget.sourcePhase (F.circuit x))
      (fun x => SourcePreparationPlacement.walkQubits (F.circuit x) (SourceCircuitSimulation.clockBits (F.circuit x)))
      (fun x => FullPrecisionBudget.sourcePrecision (F.circuit x))
      (fun x => FullPrecisionBudget.sourcePrecision (F.circuit x))
      (fun x => FullPrecisionBudget.sourcePrecision (F.circuit x))
      (fun x => FullFilterPlacement.sourceDeltaRaw (F.circuit x) (SourceCircuitSimulation.clockBits (F.circuit x))) := by
  have hδ : LogspaceComputes id (fun x =>
      (FullFilterPlacement.sourceDeltaRaw (F.circuit x) (SourceCircuitSimulation.clockBits (F.circuit x))).encode) := by
    simpa only [sourceDeltaRaw_eq_fraction] using
      reciprocal_generated classical numeric binary id
        (fun x => FullPrecisionBudget.sourceDeltaDen (F.circuit x))
        (fun x => FullPrecisionBudget.sourceDeltaDen_pos (F.circuit x)) P.deltaDen
  exact parameterQueries_of_data classical binary id _ _ _ _ _ _ P.m
    (source_walk_width_generated classical arithmetic parsing F P) P.p P.M
    (FullPrecisionBudget.sourcePhase_dimension_polynomial F) hδ P.p P.p

/-- The complete source-native UF list is uniform once its independently
compiled actual source walk is generated. The caller supplies no filter query,
angle generator, Fourier generator, or whole-filter compiler premise. -/
theorem source_nativeUF_generated {G : EffectiveGateSet} (conv : GateConvention G)
    (E : ElementaryAnalyticInputs) (classical : FLListClosure) (numeric : ClassicalDescriptionClosure)
    (grammar : InstructionDescriptionClosure) (primitive : PrimitiveDescriptionConvention conv)
    (binary : BinaryDataDescription) (shift : BinaryShiftDescription)
    (arithmetic : NatArithmeticDescription) (unary : FourierCompilation.UnaryCounterArithmetic)
    (closure : RecipeDescriptionClosure) (parsing : SourceDescriptionParsing G)
    (F : EffectiveSourceFamily G) (P : SimulatorParameterUniform.ParameterComputations F)
    (hwalk : GeneratedCircuit id (fun x => FullFilterPlacement.nativeWalk conv (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x))
      (conv.rotationRep (selectorAngle E (FullPrecisionBudget.sourcePrecision (F.circuit x)))))) :
    GeneratedCircuit id (fun x => FullFilterPlacement.nativeUF conv E (F.circuit x)
      (SourceCircuitSimulation.clockBits (F.circuit x)) (FullPrecisionBudget.sourcePhase (F.circuit x))
      (FullPrecisionBudget.sourcePrecision (F.circuit x)) (FullPrecisionBudget.sourcePrecision (F.circuit x))
      (FullPrecisionBudget.sourcePrecision (F.circuit x)) (FullPrecisionBudget.sourcePrecision (F.circuit x))) :=
  nativeUF_generated conv E classical numeric grammar primitive shift unary closure id F.circuit
    _ _ _ _ _ _ (source_parameterQueries classical numeric binary arithmetic parsing F P) hwalk

end Paper25.OperationalModel.FilterUniformCompilation
