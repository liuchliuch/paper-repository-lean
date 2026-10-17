import Paper25.RationalSourceWalkCompilation
import Paper25.CoherentCompilation
import Paper25.SourcePreparationPlacement
import Paper25.FullPrecisionBudget
import Paper25.DecisionFamilies

/-! Explicit native gate counts and polynomial closure for the actual local
compiler constructors. This file has no simulator-generation assumption. -/
noncomputable section
namespace Paper25.FullCompilationResources
open OperationalModel OperationalModel.LocalCompilation OperationalModel.CoherentCompilation
open SourceHistoryCompilation SourceWalkCompilation
variable {G : EffectiveGateSet}

def fourierCost (conv : GateConvention G) : ℕ :=
  conv.bound+conv.bound^2+3*conv.CNOT.length

def filterGateBound (conv : GateConvention G) (m walkLength : ℕ) : ℕ :=
  (conv.bound+1)*((conv.bound+1)*(m*(m+2)*fourierCost conv) +
    2^m*conv.bound^(m+1)*(2^m*walkLength)) + 2^m*conv.bound^(m+1)*conv.bound

lemma filterGateBound_mono (conv : GateConvention G) (m : ℕ) {W V : ℕ} (h : W≤V) :
    filterGateBound conv m W ≤ filterGateBound conv m V := by
  unfold filterGateBound
  gcongr

lemma labelCircuit_length (conv : GateConvention G) (m q : ℕ)
    (angle : Basis m → RationalRep) :
    (labelCircuit conv m q angle).length ≤ 2^m*conv.bound^(m+1)*conv.bound := by
  apply selectCircuit_length
  intro j
  simpa only [tensorCircuit_length,List.length_nil,Nat.add_zero] using conv.rotationRep_length (angle j)

lemma nativePE_length (conv : GateConvention G) (m : ℕ) {q : ℕ}
    (walk : EffectiveCircuit G q) (fourier : EffectiveCircuit G (m+(1+q))) :
    (nativePE conv m walk fourier).length ≤
      (conv.bound+1)*fourier.length + 2^m*conv.bound^(m+1)*(2^m*walk.length) := by
  have hs : (powerSelectCircuit conv (fun j => (SelectedFilter.bitsBinaryIndex m j).val)
      (rotationSpectator walk)).length ≤ 2^m*conv.bound^(m+1)*(2^m*walk.length) := by
    apply selectCircuit_length
    intro j
    rw [repeatCircuit_length]
    simp only [rotationSpectator,tensorCircuit_length,List.length_nil,Nat.zero_add]
    exact Nat.mul_le_mul_right _ (SelectedFilter.bitsBinaryIndex m j).isLt.le
  have ha := adjointCircuit_length conv fourier
  simp only [nativePE,phaseEstimationCircuit,List.length_append]
  nlinarith

lemma compiledFilter_length (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (precision m : ℕ) {q : ℕ} (walk : EffectiveCircuit G q) (δ : RationalRep) (n k : ℕ) :
    (compiledFilter conv E precision m walk δ n k).length ≤ filterGateBound conv m walk.length := by
  have hf := FourierCompilation.circuitOnData_gate_count_polynomial conv E precision m (1+q)
  have hp := nativePE_length conv m walk (FourierCompilation.circuitOnData conv E precision m (1+q))
  have hpe : (nativePE conv m walk (FourierCompilation.circuitOnData conv E precision m (1+q))).length ≤
      (conv.bound+1)*(m*(m+2)*fourierCost conv)+2^m*conv.bound^(m+1)*(2^m*walk.length) := by
    exact hp.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hf) _)
  have ha := adjointCircuit_length conv
    (nativePE conv m walk (FourierCompilation.circuitOnData conv E precision m (1+q)))
  have hl := labelCircuit_length conv m q (representedAngles E δ m n k)
  dsimp [compiledFilter,nativeFilter,coherentFilterCircuit]
  simp only [List.length_append]
  dsimp [filterGateBound]
  nlinarith

def walkGateBound (conv : GateConvention G) (ell : ℕ) : ℕ :=
  3*conv.X.length + (conv.bound^2+conv.bound)*encoderGateBound conv ell conv.bound +
    16*conv.bound^5*(4*(conv.X.length+conv.bound))

lemma encoderGateBound_polynomial (conv : GateConvention G) {ell p : Input → ℕ}
    (hEll : PolynomialBound (fun x => 2^ell x)) (hp : PolynomialBound p) :
    PolynomialBound (fun x => encoderGateBound conv (ell x) (p x)) := by
  have hc := control_overhead_polynomial hEll conv.bound
  have hmain := (hEll.mul hc).mul (PolynomialBound.const
    ((conv.bound+1)*(3*conv.bound)+8*conv.bound^4*
      (SourceTermCompilation.sourceTermBound conv+4*(conv.X.length+conv.bound))))
  have hinc := (hEll.pow (conv.bound+1)).mul (PolynomialBound.const conv.X.length)
  exact ((PolynomialBound.const (conv.bound+1)).mul hp).add
    ((PolynomialBound.const (2*conv.bound^2)).mul
      ((hmain.add hinc).add (PolynomialBound.const (4*(conv.X.length+conv.bound)))))

lemma walkGateBound_polynomial (conv : GateConvention G) {ell : Input → ℕ}
    (hEll : PolynomialBound (fun x => 2^ell x)) :
    PolynomialBound (fun x => walkGateBound conv (ell x)) :=
  ((PolynomialBound.const (3*conv.X.length)).add
    ((PolynomialBound.const (conv.bound^2+conv.bound)).mul
      (encoderGateBound_polynomial conv hEll (PolynomialBound.const conv.bound)))).add
        (PolynomialBound.const (16*conv.bound^5*(4*(conv.X.length+conv.bound))))

lemma filterGateBound_polynomial (conv : GateConvention G) {m W : Input → ℕ}
    (hm : PolynomialBound (fun x => 2^m x)) (hW : PolynomialBound W) :
    PolynomialBound (fun x => filterGateBound conv (m x) (W x)) := by
  have hbits : PolynomialBound m := hm.mono (fun x => Paper25.nat_le_two_pow _)
  have hc := control_overhead_polynomial hm conv.bound
  have hfourier := (hbits.mul (hbits.add (PolynomialBound.const 2))).mul (PolynomialBound.const (fourierCost conv))
  exact ((PolynomialBound.const (conv.bound+1)).mul
    (((PolynomialBound.const (conv.bound+1)).mul hfourier).add
      ((hm.mul hc).mul (hm.mul hW)))).add
        ((hm.mul hc).mul (PolynomialBound.const conv.bound))

lemma sourceClock_dimension_polynomial (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => 2^(SourceCircuitSimulation.clockBits (F.circuit x))) := by
  have h := clock_size_polynomial (SourceCircuitSimulation.duration_polynomial F)
  simpa only [SourceCircuitSimulation.clockBits,SimulationParameters.clockBits,clockSize,powerTwoCeil] using h

lemma placedF_gatePolynomial (conv : GateConvention G) (F : EffectiveSourceFamily G)
    (ell m : Input → ℕ) (t : ∀ x, StatePreparation.Bits (ell x))
    (hEll : PolynomialBound ell) :
    PolynomialBound (fun x => (SourcePreparationPlacement.placedF conv (F.circuit x) (ell x) (m x) (t x)).length) := by
  have hw : PolynomialBound (fun x => SourceCoordinates.restQubits (F.circuit x)) :=
    (logarithmic_work_dimension F.work_logarithmic).mono (fun x => by
      have h := SourceCoordinates.restQubits_add_one (F.circuit x)
      exact (show SourceCoordinates.restQubits (F.circuit x) ≤ (F.circuit x).workQubits by omega).trans
        (Paper25.nat_le_two_pow _))
  exact ((PolynomialBound.const (preparationCost conv)).mul
    ((hEll.add ((PolynomialBound.const 2).mul hw)).add (PolynomialBound.const 6))).mono
      (fun x => SourcePreparationPlacement.placedF_length conv _ _ _ _)

lemma zeroSmallReflection_gatePolynomial (conv : GateConvention G) (ell q : Input → ℕ)
    (hEll : PolynomialBound (fun x => 2^ell x)) :
    PolynomialBound (fun x => (zeroSmallReflectionCircuit conv (ell x) (q x)).length) :=
  (((control_overhead_polynomial hEll conv.bound).mul
    (PolynomialBound.const (5*conv.X.length+6*conv.bound))).add
      (PolynomialBound.const (4*(conv.X.length+conv.bound)))).mono
        (fun x => zeroSmallReflectionCircuit_length conv _ _)

theorem readout_gatePolynomial (conv : GateConvention G) {q : Input → ℕ}
    (F U R : ∀ x, EffectiveCircuit G (q x))
    (hF : PolynomialBound (fun x => (F x).length))
    (hU : PolynomialBound (fun x => (U x).length))
    (hR : PolynomialBound (fun x => (R x).length)) :
    PolynomialBound (fun x => (readoutCircuit conv
      (traceCancellationCircuit conv (coherentFilterCircuit conv (F x) (U x)) (R x))).gateCount) := by
  have hW : PolynomialBound (fun x => (coherentFilterCircuit conv (F x) (U x)).length) :=
    (((PolynomialBound.const (conv.bound+1)).mul hF).add hU).mono (fun x => by
      have ha := adjointCircuit_length conv (F x)
      simp only [coherentFilterCircuit,List.length_append]
      nlinarith)
  have hC := (hW.add ((PolynomialBound.const conv.bound).mul hR)).mono
    (fun x => traceCancellationCircuit_length conv _ _)
  exact ((PolynomialBound.const conv.bound).mul (hC.add (PolynomialBound.const 2))).mono
    (fun x => readoutCircuit_length conv _)


end Paper25.FullCompilationResources
