import Paper25.ClassicalCounterCompilation
import Paper25.FullPrecisionBudget

/-!
# Finite-transducer computation of the simulator's complete precision parameters

The only source-specific starting computations here are the unary work width
and the unary duration of the actual expanded source schedule. The source-byte
parsing layer supplies these from `F.uniform`; they are intermediate premises,
not additional external theorem inputs. Every simulator-specific arithmetic
combination is derived below from fixed classical arithmetic and FL closure.
Every exponentiation-to-unary call is discharged by the source family's proved
polynomial dimension bounds, including the chosen phase and precision budgets.
-/
noncomputable section
namespace Paper25.SimulatorParameterUniform
open OperationalModel OperationalModel.UniformCompilation SourceCoordinates FullPrecisionBudget
set_option maxHeartbeats 1000000

abbrev UnaryComputes (f : Input → ℕ) : Prop :=
  LogspaceComputes id (fun x => encodeNat (f x))

variable {G : EffectiveGateSet}

lemma sourcePhase_eq (S : EffectiveSourceComputation G) : sourcePhase S =
    phaseBits (clockSize (duration S)) (2^S.workQubits) := by
  unfold sourcePhase SelectedFilter.sourcePhaseBits SourceCircuitSimulation.clockBits
  rw [SimulationParameters.clock_card, SimulationParameters.work_card, restQubits_add_one]

lemma clockBits_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G) (hDuration : UnaryComputes (fun x => duration (F.circuit x))) :
    UnaryComputes (fun x => SourceCircuitSimulation.clockBits (F.circuit x)) := by
  have ht := nat_add classical arithmetic id (fun x => duration (F.circuit x)) (fun _ => 1)
    hDuration (nat_const classical id 1)
  exact nat_clog2 classical arithmetic id _ ht

lemma clockSize_generated (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G)
    (hEll : UnaryComputes (fun x => SourceCircuitSimulation.clockBits (F.circuit x))) :
    UnaryComputes (fun x => clockSize (duration (F.circuit x))) := by
  apply nat_two_pow arithmetic id _ hEll
  change PolynomialBound (fun x => clockSize (duration (F.circuit x)))
  exact clock_size_polynomial (SourceCircuitSimulation.duration_polynomial F)

lemma workDimension_generated (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G) (hwork : UnaryComputes (fun x => (F.circuit x).workQubits)) :
    UnaryComputes (fun x => 2^(F.circuit x).workQubits) :=
  nat_two_pow arithmetic id _ hwork (logarithmic_work_dimension F.work_logarithmic)

lemma rest_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G) (hwork : UnaryComputes (fun x => (F.circuit x).workQubits)) :
    UnaryComputes (fun x => restQubits (F.circuit x)) := by
  have heq : (fun x => restQubits (F.circuit x)) = (fun x => (F.circuit x).workQubits-1) := by
    funext x
    have h := restQubits_add_one (F.circuit x)
    omega
  rw [heq]
  exact nat_sub classical arithmetic id _ _ hwork (nat_const classical id 1)

lemma phaseRequest_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (J K : Input → ℕ) (hJ : UnaryComputes J) (hK : UnaryComputes K) :
    UnaryComputes (fun x => phaseRequest (J x) (K x)) := by
  exact nat_mul classical arithmetic id _ _
    (nat_mul classical arithmetic id _ _ (nat_const classical id 491520000000000)
      (nat_pow_const classical arithmetic id J 6 hJ))
    (nat_pow_const classical arithmetic id K 11 hK)

lemma phase_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G)
    (hJ : UnaryComputes (fun x => clockSize (duration (F.circuit x))))
    (hK : UnaryComputes (fun x => 2^(F.circuit x).workQubits)) :
    UnaryComputes (fun x => sourcePhase (F.circuit x)) := by
  simpa only [sourcePhase_eq, phaseBits, ceilLog2] using
    nat_clog2 classical arithmetic id _ (phaseRequest_generated classical arithmetic _ _ hJ hK)

lemma phaseDimension_generated (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G) (hm : UnaryComputes (fun x => sourcePhase (F.circuit x))) :
    UnaryComputes (fun x => 2^sourcePhase (F.circuit x)) :=
  nat_two_pow arithmetic id _ hm (sourcePhase_dimension_polynomial F)

lemma smallQubits_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G) (hwork : UnaryComputes (fun x => (F.circuit x).workQubits))
    (hEll : UnaryComputes (fun x => SourceCircuitSimulation.clockBits (F.circuit x)))
    (hm : UnaryComputes (fun x => sourcePhase (F.circuit x))) :
    UnaryComputes (fun x => simulatorSmallQubits (F.circuit x).workQubits (duration (F.circuit x))) := by
  have htwo := nat_mul classical arithmetic id _ _ (nat_const classical id 2) hwork
  have he := nat_add classical arithmetic id _ _ htwo hEll
  have hp := nat_add classical arithmetic id _ _ he hm
  simpa only [simulatorSmallQubits, sourcePhase_eq, SourceCircuitSimulation.clockBits,
    SimulationParameters.clockBits] using
    nat_add classical arithmetic id _ _ hp (nat_const classical id 6)

lemma smallDimension_generated (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G)
    (hk : UnaryComputes (fun x => simulatorSmallQubits (F.circuit x).workQubits (duration (F.circuit x)))) :
    UnaryComputes (fun x => 2^simulatorSmallQubits (F.circuit x).workQubits (duration (F.circuit x))) :=
  nat_two_pow arithmetic id _ hk (SourceCircuitSimulation.mixed_resources F).2

lemma gapDen_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (J K k : Input → ℕ) (hJ : UnaryComputes J) (hK : UnaryComputes K)
    (hSmall : UnaryComputes (fun x => 2^k x)) :
    UnaryComputes (fun x => gapDen (J x) (K x) (k x)) := by
  exact nat_mul classical arithmetic id _ _
    (nat_mul classical arithmetic id _ _
      (nat_mul classical arithmetic id _ _ (nat_const classical id 1600)
        (nat_pow_const classical arithmetic id J 2 hJ))
      (nat_pow_const classical arithmetic id K 4 hK)) hSmall

lemma deltaDen_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (J K : Input → ℕ) (hJ : UnaryComputes J) (hK : UnaryComputes K) :
    UnaryComputes (fun x => deltaDen (J x) (K x)) := by
  exact nat_mul classical arithmetic id _ _
    (nat_mul classical arithmetic id _ _ (nat_const classical id 300)
      (nat_pow_const classical arithmetic id J 2 hJ))
    (nat_pow_const classical arithmetic id K 3 hK)

lemma accuracyDen_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (M m d D : Input → ℕ) (hM : UnaryComputes M) (hm : UnaryComputes m)
    (hd : UnaryComputes d) (hD : UnaryComputes D) :
    UnaryComputes (fun x => accuracyDen (M x) (m x) (d x) (D x)) := by
  have hm2 := nat_add classical arithmetic id _ _ hm (nat_const classical id 2)
  have hmprod := nat_mul classical arithmetic id _ _ hm hm2
  have hleft := nat_mul classical arithmetic id _ _ (nat_const classical id 24) hM
  have hright := nat_mul classical arithmetic id _ _ (nat_const classical id 16) hmprod
  have hsum := nat_add classical arithmetic id _ _ hleft hright
  have hterm := nat_add classical arithmetic id _ _ hsum (nat_const classical id 4000)
  exact nat_mul classical arithmetic id _ _
    (nat_mul classical arithmetic id _ _
      (nat_mul classical arithmetic id _ _ (nat_const classical id 100) hterm) hd) hD

lemma precision_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (M m d D : Input → ℕ) (hM : UnaryComputes M) (hm : UnaryComputes m)
    (hd : UnaryComputes d) (hD : UnaryComputes D) :
    UnaryComputes (fun x => precision (M x) (m x) (d x) (D x)) :=
  nat_clog2 classical arithmetic id _ (accuracyDen_generated classical arithmetic M m d D hM hm hd hD)

/-- Proof-only collection of the derived parameter machines. This is constructed
below; it is never an external simulator-uniformity premise. -/
structure ParameterComputations (F : EffectiveSourceFamily G) : Prop where
  work : UnaryComputes (fun x => (F.circuit x).workQubits)
  duration : UnaryComputes (fun x => SourceCoordinates.duration (F.circuit x))
  rest : UnaryComputes (fun x => restQubits (F.circuit x))
  ell : UnaryComputes (fun x => SourceCircuitSimulation.clockBits (F.circuit x))
  J : UnaryComputes (fun x => clockSize (SourceCoordinates.duration (F.circuit x)))
  K : UnaryComputes (fun x => 2^(F.circuit x).workQubits)
  m : UnaryComputes (fun x => sourcePhase (F.circuit x))
  M : UnaryComputes (fun x => 2^sourcePhase (F.circuit x))
  ksmall : UnaryComputes (fun x => simulatorSmallQubits (F.circuit x).workQubits
    (SourceCoordinates.duration (F.circuit x)))
  smallDim : UnaryComputes (fun x => 2^simulatorSmallQubits (F.circuit x).workQubits
    (SourceCoordinates.duration (F.circuit x)))
  D : UnaryComputes (fun x => sourceD (F.circuit x))
  deltaDen : UnaryComputes (fun x => sourceDeltaDen (F.circuit x))
  accuracyDen : UnaryComputes (fun x => FullPrecisionBudget.accuracyDen
    (2^sourcePhase (F.circuit x)) (sourcePhase (F.circuit x))
    (sourceDeltaDen (F.circuit x)) (sourceD (F.circuit x)))
  p : UnaryComputes (fun x => sourcePrecision (F.circuit x))
  inverseAccuracy : UnaryComputes (fun x => 2^sourcePrecision (F.circuit x))

/-- All simulator-specific parameter machines, with every exponential-output
polynomial premise discharged by proved original-source resource bounds. -/
theorem parameters_generated (classical : FLListClosure) (arithmetic : NatArithmeticDescription)
    (F : EffectiveSourceFamily G) (hwork : UnaryComputes (fun x => (F.circuit x).workQubits))
    (hDuration : UnaryComputes (fun x => duration (F.circuit x))) : ParameterComputations F := by
  have hrest := rest_generated classical arithmetic F hwork
  have hEll := clockBits_generated classical arithmetic F hDuration
  have hJ := clockSize_generated arithmetic F hEll
  have hK := workDimension_generated arithmetic F hwork
  have hm := phase_generated classical arithmetic F hJ hK
  have hM := phaseDimension_generated arithmetic F hm
  have hsmall := smallQubits_generated classical arithmetic F hwork hEll hm
  have hdim := smallDimension_generated arithmetic F hsmall
  have hD : UnaryComputes (fun x => sourceD (F.circuit x)) :=
    gapDen_generated classical arithmetic _ _ _ hJ hK hdim
  have hd : UnaryComputes (fun x => sourceDeltaDen (F.circuit x)) :=
    deltaDen_generated classical arithmetic _ _ hJ hK
  have hacc := accuracyDen_generated classical arithmetic _ _ _ _ hM hm hd hD
  have hp : UnaryComputes (fun x => sourcePrecision (F.circuit x)) :=
    precision_generated classical arithmetic _ _ _ _ hM hm hd hD
  exact ⟨hwork,hDuration,hrest,hEll,hJ,hK,hm,hM,hsmall,hdim,hD,hd,hacc,hp,
    nat_two_pow arithmetic id _ hp (logarithmic_work_dimension (sourcePrecision_logarithmic F))⟩

end Paper25.SimulatorParameterUniform
