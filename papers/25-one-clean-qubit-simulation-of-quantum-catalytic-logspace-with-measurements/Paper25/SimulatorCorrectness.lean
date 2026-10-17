import Paper25.SimulatorCircuit
import Paper25.NativeReadoutError

/-! Error transfer for the single concrete native simulator. The source
channel and its exact restoration hypothesis are never approximated. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper25.SimulatorCircuit
open OperationalModel OperationalModel.LocalCompilation
open FullPrecisionBudget SourceCoordinates SourceSimulation SourcePreparationPlacement
variable {G : EffectiveGateSet}

/-- Exact F placement identifies the native chronological product with the
paper's readout, up to precisely the compiled filter error. -/
theorem readoutW_error_of_filter (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (C : EffectiveSourceComputation G) (D : SourceCircuitSimulation.SpectralInput C)
    (ε : ℝ)
    (hf : ‖(filter conv E C).matrix -
      (SourceCircuitSimulation.implementation C D).matrix.submatrix
        (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))
        (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))‖ ≤ ε) :
    ‖(readoutW conv E C).matrix -
      (readoutUnitary (SourceCircuitSimulation.implementation C D)
        (SourceCircuitSimulation.clock_valid C)).submatrix
          (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))
          (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))‖ ≤ ε := by
  let e := filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C)
  have hF := placedF_matrix_filterLayout conv C (SourceCircuitSimulation.clockBits C)
    (sourcePhase C) (terminalClock (SourceCircuitSimulation.clockBits C) (duration C)
      (SourceCircuitSimulation.clock_valid C))
  have hi : (readoutUnitary (SourceCircuitSimulation.implementation C D)
      (SourceCircuitSimulation.clock_valid C)).submatrix e e =
      (preparation conv C).matrix.conjTranspose *
        (SourceCircuitSimulation.implementation C D).matrix.submatrix e e := by
    simp only [preparation,hF,Matrix.conjTranspose_submatrix,Matrix.submatrix_mul_equiv,
      readoutUnitary,readoutPreparation]
    dsimp only [e]
    rw [Matrix.submatrix_mul_equiv]

  change ‖(readoutW conv E C).matrix -
    (readoutUnitary (SourceCircuitSimulation.implementation C D)
      (SourceCircuitSimulation.clock_valid C)).submatrix e e‖ ≤ ε
  rw [hi,readoutW,EffectiveCircuit.matrix_append,adjointCircuit_matrix,←mul_sub]
  calc
    _ ≤ ‖(preparation conv C).matrix.conjTranspose‖ *
        ‖(filter conv E C).matrix -
          (SourceCircuitSimulation.implementation C D).matrix.submatrix e e‖ := norm_mul_le _ _
    _ ≤ 1 * ‖(filter conv E C).matrix -
          (SourceCircuitSimulation.implementation C D).matrix.submatrix e e‖ := by
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [Matrix.l2_opNorm_conjTranspose]
      exact Synthesis.unitary_opNorm_le (preparation conv C).unitary
    _ ≤ ε := by simpa only [one_mul] using hf

/-- The actual zero-small-register reflection, mixed trace bit and final
probe transfer the component error to the target's own Born probability. -/
theorem accept_error_of_filter (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (C : EffectiveSourceComputation G) (D : SourceCircuitSimulation.SpectralInput C)
    (ε : ℝ)
    (hf : ‖(filter conv E C).matrix -
      (SourceCircuitSimulation.implementation C D).matrix.submatrix
        (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))
        (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))‖ ≤ ε) :
    |(target conv E C).accept - SourceCircuitSimulation.probability C D| ≤ 2*ε := by
  let e := filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C)
  let P := OneCleanQubit.ancillaryProjector (n := CatalystData C.catalystQubits)
    (AuxiliarySmall (SourceCircuitSimulation.clockBits C) (restQubits C) (sourcePhase C+4+1))
    (ancillaryZero (SourceCircuitSimulation.clockBits C) (restQubits C) (sourcePhase C+4+1))
  have hR : (reflection conv C).matrix = projectorReflection (P.submatrix e e) := by
    rw [reflection,FullReflectionPlacement.reflection_matrix]
    ext x y
    simp [P,e,projectorReflection,two_smul,Matrix.submatrix_apply,Matrix.one_apply,
      (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C)).injective.eq_iff]
  have h := NativeReadoutError.reflectedReadout_accept_error_reindex conv e
    (readoutW conv E C) (reflection conv C) P
    (readoutUnitary (SourceCircuitSimulation.implementation C D)
      (SourceCircuitSimulation.clock_valid C))
    (OneCleanQubit.ancillaryProjector_hermitian _ _)
    (OneCleanQubit.ancillaryProjector_idempotent _ _) hR
    (readoutUnitary_unitary _ _) ε (readoutW_error_of_filter conv E C D ε hf)
  simpa only [target,SourceCircuitSimulation.probability,targetProbability,targetTraceUnitary,P]
    using h

/-- Concrete accumulated native-filter error at the one chosen precision. -/
def compilationError (C : EffectiveSourceComputation G) : ℝ :=
  24*(2^sourcePhase C:ℕ)*bitError (sourcePrecision C) +
    16*(sourcePhase C*(sourcePhase C+2):ℕ)*bitError (sourcePrecision C) + labelError (sourceD C)

lemma compilationError_nonneg (C : EffectiveSourceComputation G) : 0 ≤ compilationError C := by
  have hp := bitError_pos (sourcePrecision C)
  have hD : (0:ℝ) < sourceD C := by exact_mod_cast sourceD_pos C
  dsimp [compilationError,labelError]
  positivity

lemma compilationError_budget (C : EffectiveSourceComputation G) :
    4*compilationError C ≤ 1/(sourceD C:ℝ) :=
  (all_budgets (2^sourcePhase C) (sourcePhase C) (sourceDeltaDen C) (sourceD C)
    (sourceDeltaDen_pos C) (sourceD_pos C)).2.2

lemma source_delta_value (C : EffectiveSourceComputation G) :
    ((FullFilterPlacement.sourceDeltaRaw C (SourceCircuitSimulation.clockBits C)).value:ℝ) =
      1/(sourceDeltaDen C:ℝ) := by
  rw [FullFilterPlacement.sourceDeltaRaw_value]
  unfold SourceCircuitSimulation.clockBits
  rw [SimulationParameters.clock_card,SimulationParameters.work_card,restQubits_add_one]
  dsimp [sourceDeltaDen,deltaDen,biasDelta,biasLam]
  push_cast
  ring

/-- Every component approximation premise is discharged for the actual UF. -/
theorem filter_error (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (C : EffectiveSourceComputation G) (D : SourceCircuitSimulation.SpectralInput C) :
    ‖(filter conv E C).matrix -
      (SourceCircuitSimulation.implementation C D).matrix.submatrix
        (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))
        (filterLayout C (SourceCircuitSimulation.clockBits C) (sourcePhase C))‖ ≤ compilationError C := by
  have hb := all_budgets (2^sourcePhase C) (sourcePhase C) (sourceDeltaDen C) (sourceD C)
    (sourceDeltaDen_pos C) (sourceD_pos C)
  have hσ : 0 ≤ labelError (sourceD C) := by
    have hD : (0:ℝ) < sourceD C := by exact_mod_cast sourceD_pos C
    dsimp [labelError]
    positivity
  have hn : bitError (sourcePrecision C) ≤
      ((FullFilterPlacement.sourceDeltaRaw C (SourceCircuitSimulation.clockBits C)).value:ℝ)*
        labelError (sourceD C)/40 := by
    rw [source_delta_value]
    exact hb.2.1
  have h := FullFilterPlacement.nativeUF_error_implementation conv E standard C D
    (sourcePrecision C) (sourcePrecision C) (sourcePrecision C) (sourcePrecision C)
    (labelError (sourceD C)) hσ hb.1 hn
  simpa only [filter,compilationError,sourcePhase] using h

/-- Actual target Born probability differs from the proved ideal matrix
simulator by at most half of its signed probability gap. -/
theorem accept_error (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (C : EffectiveSourceComputation G) (D : SourceCircuitSimulation.SpectralInput C) :
    |(target conv E C).accept - SourceCircuitSimulation.probability C D| ≤
      SourceCircuitSimulation.gap C/2 := by
  have h := accept_error_of_filter conv E C D (compilationError C)
    (filter_error conv E standard C D)
  have hb := compilationError_budget C
  have hn := compilationError_nonneg C
  exact h.trans ((by linarith : 2*compilationError C ≤ 1/(sourceD C:ℝ)).trans (sourceD_gap C))

/-- Source-to-native simulation with the actual gate list, actual clean/mixed
input and actual final probe probability; no implementation certificate is a
premise. The eigenbasis is used solely in this correctness proof. -/
theorem pointwise_simulation (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (C : EffectiveSourceComputation G) (hr : C.Restores)
    (D : SourceCircuitSimulation.SpectralInput C) :
    0 < SourceCircuitSimulation.gap C/2 ∧
      (target conv E C).mixedQubits =
        simulatorMixedQubits C.workQubits C.catalystQubits (duration C) ∧
      OneCleanQubit.Unitary (target conv E C).matrix ∧
      (0 ≤ (target conv E C).accept ∧ (target conv E C).accept ≤ 1) ∧
      (2/3 ≤ C.accept (SourceCircuitSimulation.zeroCatalyst C) →
        1/2+SourceCircuitSimulation.gap C/2 ≤ (target conv E C).accept) ∧
      (C.accept (SourceCircuitSimulation.zeroCatalyst C) ≤ 1/3 →
        (target conv E C).accept ≤ 1/2-SourceCircuitSimulation.gap C/2) := by
  have hs := SourceCircuitSimulation.pointwise_simulation C hr D
  have he := abs_le.mp (accept_error conv E standard C D)
  refine ⟨by linarith [hs.1],target_mixed_qubits conv E C,(target conv E C).unitary,
    (target conv E C).accept_mem_unitInterval,?_,?_⟩
  · intro ha
    have hp := hs.2.2.2.1 ha
    linarith
  · intro ha
    have hp := hs.2.2.2.2 ha
    linarith

/-- One reciprocal-polynomial probability separation for every complete input
string of the native family. Uniform generation is supplied by the separate
actual-description construction, rather than assumed here. -/
theorem family_probability_gap (external : UnitarySpectralTheorem)
    (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : OperationalModel.FourierCompilation.StandardQFTCorrectness)
    (F : EffectiveSourceFamily G) (language : Input → Bool)
    (hdecides : EffectiveSourceDecidesBoundedError F language) :
    ∃ (A : ℝ) (d : ℕ), 0 < A ∧ ∀ x,
      if language x then 1/2+A/((x.length:ℝ)+1)^d ≤ (target conv E (F.circuit x)).accept
      else (target conv E (F.circuit x)).accept ≤ 1/2-A/((x.length:ℝ)+1)^d := by
  obtain ⟨A,d,hA,hbound⟩ := SourceCircuitSimulation.uniform_gap_bound F
  refine ⟨A,d,hA,?_⟩
  intro x
  have hp := pointwise_simulation conv E standard (F.circuit x) (F.restoration x)
    (SourceCircuitSimulation.spectralData external (F.circuit x))
  have hdensity := SourceCircuitSimulation.zeroCatalyst_density (F.circuit x)
  have hd := hdecides x _ hdensity.1 hdensity.2
  have hb := hbound x
  cases hl : language x
  · simp only [hl,Bool.false_eq_true,↓reduceIte] at hd ⊢
    have hn := hp.2.2.2.2.2 hd
    linarith
  · simp only [hl,↓reduceIte] at hd ⊢
    have hy := hp.2.2.2.2.1 hd
    linarith

end Paper25.SimulatorCircuit
