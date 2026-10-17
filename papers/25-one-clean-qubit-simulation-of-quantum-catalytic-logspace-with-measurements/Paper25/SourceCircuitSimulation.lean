import Paper25.SourceCoordinates
import Paper25.ActualFilterImplementation
import Paper25.SimulationParameters
import Paper25.DecisionFamilies
import Paper25.ExternalInputs

/-! The actual matrix simulator for every effective source circuit, including
arbitrary output wire, real measurement/reset expansion, actual history LCU,
coherent filter, F and one-clean-probe Born measurement. The sole spectral
input is an external unitary eigenbasis; it is not runtime circuit data. -/
noncomputable section
open scoped ComplexOrder
namespace Paper25.SourceCircuitSimulation
open OperationalModel SourceCoordinates SelectedFilter SourceSimulation StatePreparation
variable {G : EffectiveGateSet}

def clockBits (C : EffectiveSourceComputation G) : ℕ :=
  SimulationParameters.clockBits (duration C)

lemma clock_valid (C : EffectiveSourceComputation G) :
    duration C+1 ≤ Fintype.card (Bits (clockBits C)) :=
  SimulationParameters.clock_valid (duration C)

def encoder (C : EffectiveSourceComputation G) :=
  sourceAEncoding (clockBits C) (restQubits C) C.catalystQubits (duration C) (canonicalK C)

abbrev SpectralInput (C : EffectiveSourceComputation G) :=
  UnitaryEigenbasis (blockWalk (encoder C) (0, zeroSelector3))

lemma encoder_unitary (C : EffectiveSourceComputation G) :
    encoder C ∈ Matrix.unitaryGroup _ ℂ :=
  HistoryEncoding.enumeratedAEncoding_unitary (canonicalK C)
    (fun t _ j => canonicalK_unitary C t j)

lemma walk_unitary (C : EffectiveSourceComputation G) :
    blockWalk (encoder C) (0, zeroSelector3) ∈ Matrix.unitaryGroup _ ℂ := by
  apply compressionWalk_unitary
  · exact isometryProjector_hermitian _
  · exact isometryProjector_sq _ (blockColumn_isometry _)
  · exact hermitianDilation_unitary _ (encoder_unitary C)

/-- This use of the external theorem is purely in the correctness proof;
the implemented matrix is independent of the chosen spectral data. -/
def spectralData (external : UnitarySpectralTheorem) (C : EffectiveSourceComputation G) :
    SpectralInput C := Classical.choice (external.eigenbasis _ _ (walk_unitary C))

def implementation (C : EffectiveSourceComputation G) (D : SpectralInput C) :=
  coherentSourceImplementation (clockBits C) (restQubits C) C.catalystQubits (duration C)
    (canonicalSteps C) (clock_valid C) (canonicalK C)
      (fun t _ j => canonicalK_unitary C t j) (fun t _ => canonicalK_average C t) D

def probability (C : EffectiveSourceComputation G) (D : SpectralInput C) : ℝ :=
  targetProbability (implementation C D) (clock_valid C)

def gap (C : EffectiveSourceComputation G) : ℝ :=
  targetGap (clockBits C) (restQubits C) (sourcePhaseBits (clockBits C) (restQubits C)+4+1)

/-- Spectral vectors are solely proof data. The simulator itself is independent
of which orthonormal eigenbasis witnesses the external spectral theorem. -/
lemma implementation_independent (C : EffectiveSourceComputation G)
    (D E : SpectralInput C) : (implementation C D).matrix = (implementation C E).matrix := rfl

lemma probability_independent (C : EffectiveSourceComputation G)
    (D E : SpectralInput C) : probability C D = probability C E := rfl

def zeroCatalyst (C : EffectiveSourceComputation G) : Operator C.catalystQubits :=
  Matrix.single (zeroBits C.catalystQubits) (zeroBits C.catalystQubits) 1

lemma zeroCatalyst_density (C : EffectiveSourceComputation G) : IsDensity (zeroCatalyst C) := by
  unfold zeroCatalyst
  rw [← SourceReduction.cleanWork_eq_single]
  constructor
  · apply Matrix.PosSemidef.diagonal
    intro i
    change (0:ℂ) ≤ (if i = zeroBits C.catalystQubits then 1 else 0)
    split_ifs <;> norm_num
  · simp [SourceBias.cleanWork, Matrix.trace, Matrix.diag]

theorem pointwise_simulation (C : EffectiveSourceComputation G) (hr : C.Restores)
    (D : SpectralInput C) :
    0 < gap C ∧
      OneCleanQubit.Unitary (OneCleanQubit.circuit
        (targetTraceUnitary (implementation C D) (clock_valid C))) ∧
      (0 ≤ probability C D ∧ probability C D ≤ 1) ∧
      (2/3 ≤ C.accept (zeroCatalyst C) → 1/2+gap C ≤ probability C D) ∧
      (C.accept (zeroCatalyst C) ≤ 1/3 → probability C D ≤ 1/2-gap C) := by
  have h := source_probability_gap_actual_filter (clockBits C) (restQubits C)
    C.catalystQubits (duration C) (canonicalSteps C) (clock_valid C)
      (canonical_steps_restores C hr) (canonicalK C)
        (fun t _ j => canonicalK_unitary C t j) (fun t _ => canonicalK_average C t) D
  simpa only [canonical_sourceProbability, gap, probability, implementation, zeroCatalyst] using h

lemma physical_small_qubits (C : EffectiveSourceComputation G) :
    smallQubits (clockBits C) (restQubits C)
      (sourcePhaseBits (clockBits C) (restQubits C)+4+1) =
        simulatorSmallQubits C.workQubits (duration C) := by
  have h := SimulationParameters.small_qubits (restQubits C) (duration C)
  rw [restQubits_add_one] at h
  exact h

lemma physical_mixed_qubits (C : EffectiveSourceComputation G) :
    C.catalystQubits+C.catalystQubits+
      smallQubits (clockBits C) (restQubits C)
        (sourcePhaseBits (clockBits C) (restQubits C)+4+1)+1 =
      simulatorMixedQubits C.workQubits C.catalystQubits (duration C) := by
  rw [physical_small_qubits]
  unfold simulatorMixedQubits
  omega

lemma duration_polynomial (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => duration (F.circuit x)) :=
  ((PolynomialBound.const 3).mul F.gates_polynomial).mono (fun x => duration_le _)

theorem mixed_resources (F : EffectiveSourceFamily G) :
    PolynomialBound (fun x => simulatorMixedQubits (F.circuit x).workQubits
      (F.circuit x).catalystQubits (duration (F.circuit x))) ∧
    PolynomialBound (fun x => 2^simulatorSmallQubits (F.circuit x).workQubits
      (duration (F.circuit x))) :=
  ⟨mixed_qubits_polynomial F.work_logarithmic F.catalyst_polynomial (duration_polynomial F),
    small_register_dimension_polynomial F.work_logarithmic (duration_polynomial F)⟩

lemma half_gap_formula (C : EffectiveSourceComputation G) :
    gap C / 2 = biasLam (clockSize (duration C)) (2^C.workQubits : ℕ) /
      ((2:ℝ)^(simulatorSmallQubits C.workQubits (duration C)+4)*
        Real.sqrt (2^C.workQubits : ℕ)) := by
  unfold gap targetGap
  rw [physical_small_qubits]
  rw [SimulationParameters.work_card, restQubits_add_one]
  change biasLam (Fintype.card (Bits (SimulationParameters.clockBits (duration C))))
    (2^C.workQubits : ℕ) / _ / 2 = _
  rw [SimulationParameters.clock_card]
  rw [div_div]
  have hp (k : ℕ) : (2:ℝ)^(k+4) = (2:ℝ)^(k+3)*2 := by rw [show k+4=k+3+1 by omega, pow_succ]
  rw [hp]
  congr 1
  ring

theorem uniform_gap_bound (F : EffectiveSourceFamily G) :
    ∃ (A : ℝ) (d : ℕ), 0 < A ∧ ∀ x,
      A / ((x.length:ℝ)+1)^d ≤ gap (F.circuit x) / 2 := by
  obtain ⟨A,d,hA,hbound⟩ := string_gap_inverse_polynomial
    (clock_size_polynomial (duration_polynomial F))
    (logarithmic_work_dimension F.work_logarithmic) (mixed_resources F).2
    (fun _ => powerTwoCeil_pos _) (fun _ => Nat.two_pow_pos _)
  refine ⟨A,d,hA,?_⟩
  intro x
  rw [half_gap_formula]
  exact hbound x

/-- Uniform signed separation of the true matrix simulator, with one common
reciprocal-polynomial bound for every input string. Local-gate generation is
proved separately and is not asserted by this matrix-level family theorem. -/
theorem matrix_family_signed_gap (external : UnitarySpectralTheorem)
    (F : EffectiveSourceFamily G) (language : Input → Bool)
    (hdecides : EffectiveSourceDecidesBoundedError F language) :
    ∃ (A : ℝ) (d : ℕ), 0 < A ∧ ∀ x,
      if language x then 1/2 + A/((x.length:ℝ)+1)^d ≤
        probability (F.circuit x) (spectralData external (F.circuit x))
      else probability (F.circuit x) (spectralData external (F.circuit x)) ≤
        1/2 - A/((x.length:ℝ)+1)^d := by
  obtain ⟨A,d,hA,hbound⟩ := uniform_gap_bound F
  refine ⟨A,d,hA,?_⟩
  intro x
  have hs := pointwise_simulation (F.circuit x) (F.restoration x)
    (spectralData external (F.circuit x))
  have hdensity := zeroCatalyst_density (F.circuit x)
  have hd := hdecides x _ hdensity.1 hdensity.2
  have hb := hbound x
  cases hl : language x
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hd ⊢
    have hp := hs.2.2.2.2 hd
    linarith [hs.1]
  · simp only [hl, ↓reduceIte] at hd ⊢
    have hp := hs.2.2.2.1 hd
    linarith [hs.1]

/-- Final decision transfer for a generated actual target family once its
compile-time error bound has been proved. The probability is the target's
own density semantics. This lemma alone asserts no compiler existence. -/
theorem target_family_decides_of_error (external : UnitarySpectralTheorem)
    (F : EffectiveSourceFamily G) (language : Input → Bool)
    (hdecides : EffectiveSourceDecidesBoundedError F language)
    {H : EffectiveGateSet} (target : EffectiveTargetFamily H)
    (herror : ∀ x, |target.accept x - probability (F.circuit x)
      (spectralData external (F.circuit x))| ≤ gap (F.circuit x)/2) :
    EffectiveDecidesWithInversePolynomialBias target language := by
  obtain ⟨A,d,hA,hbound⟩ := uniform_gap_bound F
  refine ⟨2*A,d,by positivity,?_⟩
  intro x
  have hs := pointwise_simulation (F.circuit x) (F.restoration x)
    (spectralData external (F.circuit x))
  have hdensity := zeroCatalyst_density (F.circuit x)
  have hd := hdecides x _ hdensity.1 hdensity.2
  have hb := hbound x
  have he := abs_le.mp (herror x)
  simp only [EffectiveTargetFamily.signedBias]
  simp only [mul_div_assoc]
  cases hl : language x
  · simp only [hl, Bool.false_eq_true, ↓reduceIte] at hd ⊢
    have hp := hs.2.2.2.2 hd
    linarith
  · simp only [hl, ↓reduceIte] at hd ⊢
    have hp := hs.2.2.2.1 hd
    linarith

end Paper25.SourceCircuitSimulation
