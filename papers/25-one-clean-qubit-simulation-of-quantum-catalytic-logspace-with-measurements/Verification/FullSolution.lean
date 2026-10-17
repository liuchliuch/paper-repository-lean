import Paper25.CompleteSimulation
import Paper25.SimulatorCorrectness
import Paper25.RestorationCP
import Paper25.SourceCircuitSimulation
import Paper25.ReflectionCompilation
import Paper25.StatePreparationLocal

/-! Independent full-scope operational contracts, including the complete actual
uniform native simulator relative to explicitly disclosed published inputs.
Challenge placeholders are isolated from all production imports. -/
noncomputable section
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
namespace Paper25.FullChallenge

theorem lemma2_restoration {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V] (v0 : V)
    (Psi : Matrix V V ℂ →ₗ[ℂ] Matrix (W × V) (W × V) ℂ)
    (hpositive : ∀ X : Matrix (V × V) (V × V) ℂ,
      X.PosSemidef → (referenceExtension Psi X).PosSemidef)
    (hrestore : ∀ rho, IsDensity rho → workPartialTrace (Psi rho) = rho) :
    ∃ eta : Matrix W W ℂ, IsDensity eta ∧ ∀ X, Psi X = Matrix.kronecker eta X :=
  Paper25.lemma_2_semantic_restoration v0 Psi hpositive hrestore

theorem lemma3_kraus_frobenius {n : Type*} [Fintype n] [DecidableEq n] (C : KrausChannel n) :
    entryNormSq C.liouville ≤ (Fintype.card n : ℝ)^2 :=
  Paper25.KrausChannel.liouville_frob_bound_card C

theorem lemma4_matrix {m : ℕ} (A : Matrix (Fin m) (Fin m) ℂ) (hA : IsUnit A)
    (lam : ℝ) (hlam : 0 < lam) :
    nuclearNorm (A⁻¹-regInv A lam) ≤ (lam/2)*frobNormSq A⁻¹ :=
  Paper25.lemma_4 A hA lam hlam

theorem lemma5_global_coherent_filter {n : Type*} [Fintype n] [DecidableEq n]
    (V : Matrix n n ℂ) (D : UnitaryEigenbasis V)
    (M : ℕ) (hM : 0 < M) (delta eps : ℝ)
    (hd : 0 < delta) (hdl : delta ≤ 1) (he : 0 < eps) (hel : eps ≤ 1)
    (hprecision : 4096/(delta*eps^2) ≤ (M:ℝ)) :
    ‖(coherentWalkFilter V M delta).submatrix
      (fun i => Sum.inl ((⟨0,hM⟩ : Fin M),i))
      (fun i => Sum.inl ((⟨0,hM⟩ : Fin M),i)) - filterRat (walkRealPart V) delta‖ ≤ eps/8 :=
  Paper25.coherentWalkFilter_error V D M hM delta eps hd hdl he hel hprecision

theorem lemma6_born_readout {n : Type*} [Fintype n] [DecidableEq n] [Nonempty n]
    (P W : Matrix n n ℂ) (hP : P.IsHermitian) (hPP : P*P=P)
    (hW : OneCleanQubit.Unitary W) :
    OneCleanQubit.Unitary (OneCleanQubit.circuit (OneCleanQubit.reflectedTraceUnitary P W)) ∧
      (0 ≤ OneCleanQubit.probZero (OneCleanQubit.output (OneCleanQubit.reflectedTraceUnitary P W)) ∧
        OneCleanQubit.probZero (OneCleanQubit.output (OneCleanQubit.reflectedTraceUnitary P W)) ≤ 1) ∧
      OneCleanQubit.expectationZ (OneCleanQubit.output (OneCleanQubit.reflectedTraceUnitary P W)) =
        (Matrix.trace (P*W)).re / Fintype.card n :=
  Paper25.OneCleanQubit.ancillary_block_readout P W hP hPP hW

theorem source_circuit_born_gap {G : OperationalModel.EffectiveGateSet}
    (C : OperationalModel.EffectiveSourceComputation G) (hr : C.Restores)
    (D : SourceCircuitSimulation.SpectralInput C) :
    0 < SourceCircuitSimulation.gap C ∧
      OneCleanQubit.Unitary (OneCleanQubit.circuit
        (SourceSimulation.targetTraceUnitary (SourceCircuitSimulation.implementation C D)
          (SourceCircuitSimulation.clock_valid C))) ∧
      (0 ≤ SourceCircuitSimulation.probability C D ∧ SourceCircuitSimulation.probability C D ≤ 1) ∧
      (2/3 ≤ C.accept (SourceCircuitSimulation.zeroCatalyst C) →
        1/2+SourceCircuitSimulation.gap C ≤ SourceCircuitSimulation.probability C D) ∧
      (C.accept (SourceCircuitSimulation.zeroCatalyst C) ≤ 1/3 →
        SourceCircuitSimulation.probability C D ≤ 1/2-SourceCircuitSimulation.gap C) :=
  Paper25.SourceCircuitSimulation.pointwise_simulation C hr D

theorem matrix_family_signed_gap {G : OperationalModel.EffectiveGateSet}
    (external : UnitarySpectralTheorem) (F : OperationalModel.EffectiveSourceFamily G)
    (language : OperationalModel.Input → Bool)
    (hdecides : OperationalModel.EffectiveSourceDecidesBoundedError F language) :
    ∃ (A : ℝ) (d : ℕ), 0 < A ∧ ∀ x,
      if language x then 1/2+A/((x.length:ℝ)+1)^d ≤
        SourceCircuitSimulation.probability (F.circuit x)
          (SourceCircuitSimulation.spectralData external (F.circuit x))
      else SourceCircuitSimulation.probability (F.circuit x)
          (SourceCircuitSimulation.spectralData external (F.circuit x)) ≤
        1/2-A/((x.length:ℝ)+1)^d :=
  Paper25.SourceCircuitSimulation.matrix_family_signed_gap external F language hdecides

theorem native_dilation {G : OperationalModel.EffectiveGateSet}
    (conv : OperationalModel.LocalCompilation.GateConvention G) {q : ℕ}
    (C : OperationalModel.EffectiveCircuit G q) :
    (OperationalModel.LocalCompilation.dilationCircuit conv C).matrix =
      (hermitianDilation C.matrix).submatrix
        (OperationalModel.probeBasis q) (OperationalModel.probeBasis q) :=
  Paper25.OperationalModel.LocalCompilation.dilationCircuit_matrix conv C

theorem native_zero_reflection {G : OperationalModel.EffectiveGateSet}
    (conv : OperationalModel.LocalCompilation.GateConvention G) (ell q : ℕ) :
    (OperationalModel.LocalCompilation.zeroReflectionCircuit conv ell q).matrix =
      (projectorReflection (OneCleanQubit.ancillaryProjector
        (n := OperationalModel.Basis (q+1)) (OperationalModel.Basis ell) (fun _ => 0))).submatrix
          (OperationalModel.registerBasis ell (q+1)) (OperationalModel.registerBasis ell (q+1)) :=
  Paper25.OperationalModel.LocalCompilation.zeroReflectionCircuit_matrix conv ell q

theorem native_source_born_gap {G : OperationalModel.EffectiveGateSet}
    (conv : OperationalModel.LocalCompilation.GateConvention G)
    (E : OperationalModel.ElementaryAnalyticInputs)
    (standard : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (C : OperationalModel.EffectiveSourceComputation G) (hr : C.Restores)
    (D : SourceCircuitSimulation.SpectralInput C) :
    0 < SourceCircuitSimulation.gap C/2 ∧
      (SimulatorCircuit.target conv E C).mixedQubits =
        simulatorMixedQubits C.workQubits C.catalystQubits (SourceCoordinates.duration C) ∧
      OneCleanQubit.Unitary (SimulatorCircuit.target conv E C).matrix ∧
      (0 ≤ (SimulatorCircuit.target conv E C).accept ∧ (SimulatorCircuit.target conv E C).accept ≤ 1) ∧
      (2/3 ≤ C.accept (SourceCircuitSimulation.zeroCatalyst C) →
        1/2+SourceCircuitSimulation.gap C/2 ≤ (SimulatorCircuit.target conv E C).accept) ∧
      (C.accept (SourceCircuitSimulation.zeroCatalyst C) ≤ 1/3 →
        (SimulatorCircuit.target conv E C).accept ≤ 1/2-SourceCircuitSimulation.gap C/2) :=
  SimulatorCircuit.pointwise_simulation conv E standard C hr D

theorem native_description_uniformity {G : OperationalModel.EffectiveGateSet}
    (conv : OperationalModel.LocalCompilation.GateConvention G)
    (E : OperationalModel.ElementaryAnalyticInputs)
    (classical : ClassicalSimulationInputs G)
    (primitive : OperationalModel.UniformCompilation.PrimitiveDescriptionConvention conv)
    (F : OperationalModel.EffectiveSourceFamily G) :
    OperationalModel.LogspaceGenerates
      (fun x => (SimulatorCircuit.target conv E (F.circuit x)).encode) :=
  CompleteSimulation.target_logspace conv E classical primitive F

theorem full_uniform_simulation {G : OperationalModel.EffectiveGateSet}
    (spectral : UnitarySpectralTheorem)
    (conv : OperationalModel.LocalCompilation.GateConvention G)
    (E : OperationalModel.ElementaryAnalyticInputs)
    (fourier : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (classical : ClassicalSimulationInputs G)
    (primitive : OperationalModel.UniformCompilation.PrimitiveDescriptionConvention conv)
    (F : OperationalModel.EffectiveSourceFamily G) (language : OperationalModel.Input → Bool)
    (hdecides : OperationalModel.EffectiveSourceDecidesBoundedError F language) :
    ∃ Q : OperationalModel.EffectiveTargetFamily G,
      (∀ x, Q.circuit x = SimulatorCircuit.target conv E (F.circuit x)) ∧
      OperationalModel.EffectiveDecidesWithInversePolynomialBias Q language :=
  CompleteSimulation.theorem1 spectral conv E fourier classical primitive F language hdecides

theorem full_exact_simulation {G : OperationalModel.EffectiveGateSet}
    (spectral : UnitarySpectralTheorem)
    (conv : OperationalModel.LocalCompilation.GateConvention G)
    (E : OperationalModel.ElementaryAnalyticInputs)
    (fourier : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (classical : ClassicalSimulationInputs G)
    (primitive : OperationalModel.UniformCompilation.PrimitiveDescriptionConvention conv)
    (F : OperationalModel.EffectiveSourceFamily G) (language : OperationalModel.Input → Bool)
    (hdecides : OperationalModel.EffectiveSourceDecidesExact F language) :
    ∃ Q : OperationalModel.EffectiveTargetFamily G,
      (∀ x, Q.circuit x = SimulatorCircuit.target conv E (F.circuit x)) ∧
      OperationalModel.EffectiveDecidesWithInversePolynomialBias Q language :=
  CompleteSimulation.theorem1_exact spectral conv E fourier classical primitive F language hdecides

end Paper25.FullChallenge
