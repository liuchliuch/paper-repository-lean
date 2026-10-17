import Paper25.SourceReduction
import Paper25.SelectedFilter
import Paper25.SelectedPreparation
import Paper25.OperationalDecision

/-! Mathematical assembly of the source-channel reduction and spectral-filter
readout. Source restoration and all CPTP/history hypotheses are discharged from
real Kraus semantics. A full filter implementation is an explicitly named
remaining implementation input; no selected-trace or final-bias estimate is
accepted from the caller. -/

noncomputable section
set_option maxHeartbeats 1200000
open scoped ComplexOrder ComplexConjugate Matrix.Norms.L2Operator
open Matrix
namespace Paper25.SourceSimulation
open SourceBias SelectedFilter

abbrev HistorySpace (α V : Type*) [Fintype α] [Fintype V] (J : ℕ) :=
  Fin J × (Fin ((Fintype.card (Work α)) ^ 2) × Fin ((Fintype.card V) ^ 2))

abbrev DilationSpace (α V : Type*) [Fintype α] [Fintype V] (J : ℕ) :=
  Fin (Fintype.card (HistorySpace α V J)) ⊕ Fin (Fintype.card (HistorySpace α V J))

def sourceHistoryMatrix {α V : Type*} [Fintype α] [Fintype V]
    [DecidableEq α] [DecidableEq V]
    (C : ℕ → KrausChannel (Work α × V)) (T J : ℕ) :
    Matrix (HistorySpace α V J) (HistorySpace α V J) ℂ :=
  1 - historyShift T J (SourceReduction.coordinates C)

/-- The actual selected history-filter amplitude, with the signed output
observable and clean work input already fixed. -/
def selectedAmplitude {α V : Type*} [Fintype α] [Fintype V] [DecidableEq α]
    {T J : ℕ} (hJ : T + 1 ≤ J) (w0 : Work α)
    (G : Matrix (DilationSpace α V J) (DilationSpace α V J) ℂ) : ℝ :=
  normalizedReTrace (selectedBlock
    (dilationOutput (historyColumn (n := (Fintype.card V)^2)
      (⟨T,by omega⟩ : Fin J) (historyZ (α := α)))) G
    (dilationInput (historyColumn (n := (Fintype.card V)^2)
      (⟨0,by omega⟩ : Fin J) (historyOmega w0))))

/-- Equation (19) for actual source channels. The only approximation premise
is on the whole filtered dilation; every restoration, channel-norm, selected
block, and source-acceptance premise is proved in this theorem. -/
theorem source_filter_error {α V : Type*} [Fintype α] [Fintype V]
    [DecidableEq α] [DecidableEq V] [Nonempty α]
    (C : ℕ → KrausChannel (Work α × V)) (w0 : Work α) (v0 : V)
    (T J : ℕ) (hJ : T + 1 ≤ J)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace ((KrausChannel.sequence C 0 T).act
        (Matrix.kronecker (Matrix.single w0 w0 1) ρ)) = ρ) :
    ∃ η : Matrix (Work α) (Work α) ℂ, IsDensity η ∧
      (∀ σ : Matrix V V ℂ, Matrix.trace σ = 1 →
        SourceReduction.sourceAccept ((KrausChannel.sequence C 0 T).act
          (Matrix.kronecker (Matrix.single w0 w0 1) σ)) = SourceBias.accept η) ∧
      ∀ (lam : ℝ), 0 < lam → ∀ (eps : ℝ)
        (G : Matrix (DilationSpace α V J) (DilationSpace α V J) ℂ),
        ‖G - idealFilter (sourceHistoryMatrix C T J) lam‖ ≤ eps →
        |selectedAmplitude hJ w0 G -
          lam * (2 * SourceBias.accept η - 1) / Real.sqrt (Fintype.card (Work α))| ≤
          (lam^2/2) * (J : ℝ)^2 * (Fintype.card (Work α) : ℝ)^2 + eps := by
  classical
  let eW := operatorIndex (Work α)
  let eV := operatorIndex V
  obtain ⟨η,hη,hproduct,hcol⟩ := lemma_2_source_exactRestoration
    (KrausChannel.sequence C 0 T) w0 v0 hrestore eW eV
  refine ⟨η,hη,?_,?_⟩
  · intro σ hσ
    rw [hproduct]
    exact SourceReduction.sourceAccept_product η σ hσ
  · intro lam hlam eps G hG
    have hrest : ExactRestoration (chainProd (SourceReduction.coordinates C) 0 T)
        (historyOmega w0) (historyEta η) := by
      rw [sourceLiouville_sequence, ← chainProd_submatrix_equiv] at hcol
      simpa only [SourceReduction.coordinates, historyOmega, historyEta,
        SourceReduction.cleanWork_eq_single, vecOp, operatorVec, eW, eV] using hcol
    have hb := sourceLiouville_cptpFrobBound C (eW.prodCongr eV) T
    have hd : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨v0⟩
    exact eq19_source_signed_bias (SourceReduction.coordinates C) hJ hd hb w0 η
      hη.1.isHermitian hη.2 hrest lam hlam eps G hG

/-- Equation (22), with the paper's explicit parameter choices (21), on the
same source and full-space filter. No final trace-error estimate is assumed. -/
theorem source_filter_budget {α V : Type*} [Fintype α] [Fintype V]
    [DecidableEq α] [DecidableEq V] [Nonempty α]
    (C : ℕ → KrausChannel (Work α × V)) (w0 : Work α) (v0 : V)
    (T J : ℕ) (hJ : T + 1 ≤ J)
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace ((KrausChannel.sequence C 0 T).act
        (Matrix.kronecker (Matrix.single w0 w0 1) ρ)) = ρ) :
    ∃ η : Matrix (Work α) (Work α) ℂ, IsDensity η ∧
      (∀ σ : Matrix V V ℂ, Matrix.trace σ = 1 →
        SourceReduction.sourceAccept ((KrausChannel.sequence C 0 T).act
          (Matrix.kronecker (Matrix.single w0 w0 1) σ)) = SourceBias.accept η) ∧
      ∀ G : Matrix (DilationSpace α V J) (DilationSpace α V J) ℂ,
        ‖G - idealFilter (sourceHistoryMatrix C T J)
          (biasLam J (Fintype.card (Work α)))‖ ≤ biasEps J (Fintype.card (Work α)) →
        |selectedAmplitude hJ w0 G -
          biasLam J (Fintype.card (Work α)) * (2 * SourceBias.accept η - 1) /
            Real.sqrt (Fintype.card (Work α))| ≤
          biasLam J (Fintype.card (Work α)) / (100 * (Fintype.card (Work α) : ℝ)) := by
  obtain ⟨η,hη,haccept,herror⟩ := source_filter_error C w0 v0 T J hJ hrestore
  refine ⟨η,hη,haccept,?_⟩
  intro G hG
  have hJone : (1 : ℝ) ≤ J := by exact_mod_cast (show 1 ≤ J by omega)
  have hKone : (1 : ℝ) ≤ Fintype.card (Work α) := by
    exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty (Work α))
  have hlam := biasLam_pos (lt_of_lt_of_le zero_lt_one hJone)
    (lt_of_lt_of_le zero_lt_one hKone)
  exact (herror _ hlam _ G hG).trans (bias_error_budget _ _ hJone hKone)


/-- Operational readout for a finite ancillary register, expressed using its
cardinality. This is the same one-clean-probe density circuit as Lemma 6. -/
theorem operational_cardinality_gap {a n : Type*} [Fintype a] [Fintype n]
    [DecidableEq a] [DecidableEq n] [Nonempty a] [Nonempty n]
    (q : a) (W : Matrix (a × n) (a × n) ℂ) (hW : OneCleanQubit.Unitary W)
    (lam K p : ℝ) (hlam : 0 < lam) (hK : 1 ≤ K)
    (herr : |normalizedReTrace (W.submatrix (fun i => (q,i)) (fun i => (q,i))) -
      lam * (2*p-1) / Real.sqrt K| ≤ lam/(100*K)) :
    let P := OneCleanQubit.ancillaryProjector (n := n) a q
    let pTarget := OneCleanQubit.probZero
      (OneCleanQubit.output (OneCleanQubit.reflectedTraceUnitary P W))
    (2/3 ≤ p → 1/2 + lam/(8*(Fintype.card a : ℝ)*Real.sqrt K) ≤ pTarget) ∧
    (p ≤ 1/3 → pTarget ≤ 1/2 - lam/(8*(Fintype.card a : ℝ)*Real.sqrt K)) := by
  classical
  dsimp only
  let P := OneCleanQubit.ancillaryProjector (n := n) a q
  let R := OneCleanQubit.reflectedTraceUnitary P W
  let b := normalizedReTrace (W.submatrix (fun i => (q,i)) (fun i => (q,i)))
  have hR := OneCleanQubit.reflectedTraceUnitary_unitary P W
    (OneCleanQubit.ancillaryProjector_hermitian _ _)
    (OneCleanQubit.ancillaryProjector_idempotent _ _) hW
  have hexp := (OneCleanQubit.ancillary_block_readout P W
    (OneCleanQubit.ancillaryProjector_hermitian _ _)
    (OneCleanQubit.ancillaryProjector_idempotent _ _) hW).2.2
  rw [OneCleanQubit.trace_ancillaryProjector] at hexp
  have hcardA : (Fintype.card a : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := a)
  have hcardN : (Fintype.card n : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero (α := n)
  have he : OneCleanQubit.expectationZ (OneCleanQubit.output R) =
      b / (Fintype.card a : ℝ) := by
    rw [hexp]
    simp only [Fintype.card_prod, Nat.cast_mul]
    dsimp [b,normalizedReTrace]
    field_simp
  have hpTarget : OneCleanQubit.probZero (OneCleanQubit.output R) =
      1/2 + b / (2*(Fintype.card a : ℝ)) := by
    have hb := OneCleanQubit.output_signedBias R hR
    rw [he] at hb
    have hd : b/(Fintype.card a : ℝ) = 2*(b/(2*(Fintype.card a : ℝ))) := by
      field_simp
    rw [hd] at hb
    linarith
  have hApos : 0 < (Fintype.card a : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : 0 < Real.sqrt K := Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hK)
  have hscale : (lam/(4*Real.sqrt K))/(2*(Fintype.card a : ℝ)) =
      lam/(8*(Fintype.card a : ℝ)*Real.sqrt K) := by
    field_simp
    <;> ring
  change (2/3 ≤ p → _ ≤ OneCleanQubit.probZero (OneCleanQubit.output R)) ∧
    (p ≤ 1/3 → OneCleanQubit.probZero (OneCleanQubit.output R) ≤ _)
  rw [hpTarget]
  constructor
  · intro hp
    have hpos : 0 < 2*p-1 := by linarith
    have habs : (1/3:ℝ) ≤ |2*p-1| := by rw [abs_of_pos hpos]; linarith
    have hg := (theorem1_decision_gap lam K (2*p-1) b hlam hK habs herr).1 hpos
    have hd := div_le_div_of_nonneg_right hg (by positivity : 0 ≤ 2*(Fintype.card a : ℝ))
    rw [hscale] at hd
    linarith
  · intro hp
    have hneg : 2*p-1 < 0 := by linarith
    have habs : (1/3:ℝ) ≤ |2*p-1| := by rw [abs_of_neg hneg]; linarith
    have hg := (theorem1_decision_gap lam K (2*p-1) b hlam hK habs herr).2 hneg
    have hd := div_le_div_of_nonneg_right hg (by positivity : 0 ≤ 2*(Fintype.card a : ℝ))
    have hscale' : (-lam/(4*Real.sqrt K))/(2*(Fintype.card a : ℝ)) =
        -lam/(8*(Fintype.card a : ℝ)*Real.sqrt K) := by
      rw [neg_div, neg_div, hscale, neg_div]
    rw [hscale'] at hd
    simp only [neg_div] at hd
    linarith

open StatePreparation

abbrev AuxiliarySmall (ell s r : ℕ) := Bits r × Small ell s 0
abbrev CatalystData (c : ℕ) := Fin ((Fintype.card (Bits c))^2)
abbrev FilterSpace (ell s c r : ℕ) := AuxiliarySmall ell s r × CatalystData c

instance filterSpaceFintype (ell s c r : ℕ) : Fintype (FilterSpace ell s c r) :=
  inferInstanceAs (Fintype (AuxiliarySmall ell s r × CatalystData c))

instance auxiliarySmallDecidableEq (ell s r : ℕ) : DecidableEq (AuxiliarySmall ell s r) :=
  @instDecidableEqProd (Bits r) (StatePreparation.Small ell s 0)
    (bitsDecidableEq r) (inferInstanceAs (DecidableEq (StatePreparation.Small ell s 0)))
instance filterSpaceDecidableEq (ell s c r : ℕ) : DecidableEq (FilterSpace ell s c r) :=
  @instDecidableEqProd (AuxiliarySmall ell s r) (CatalystData c)
    (auxiliarySmallDecidableEq ell s r) inferInstance

def ancillaryZero (ell s r : ℕ) : AuxiliarySmall ell s r :=
  (zeroBits r,smallZero ell s 0)

instance catalystDataNonempty (c : ℕ) : Nonempty (CatalystData c) :=
  ⟨⟨0,pow_pos (Fintype.card_pos_iff.mpr ⟨zeroBits c⟩) 2⟩⟩

/-- Compress only the filter's block/phase/rotation auxiliary register. -/
def auxiliaryBlock {ell s c r : ℕ}
    (U : Matrix (FilterSpace ell s c r) (FilterSpace ell s c r) ℂ) :
    Matrix (Small ell s 0 × CatalystData c) (Small ell s 0 × CatalystData c) ℂ :=
  U.submatrix (fun p => ((zeroBits r,p.1),p.2))
    (fun p => ((zeroBits r,p.1),p.2))

/-- Full filtered dilation after the explicit physical register-coordinate
change; no history selection has been made here. -/
def implementedFilterBlock {ell s c r : ℕ}
    (U : Matrix (FilterSpace ell s c r) (FilterSpace ell s c r) ℂ) :
    Matrix (PhysicalDilation ell s ((Fintype.card (Bits c))^2))
      (PhysicalDilation ell s ((Fintype.card (Bits c))^2)) ℂ :=
  (auxiliaryBlock U).submatrix (physicalDilationIndex ell s ((Fintype.card (Bits c))^2)).symm
    (physicalDilationIndex ell s ((Fintype.card (Bits c))^2)).symm

/-- Explicit remaining implementation input. Its matrix acts on the actual
qubit registers and is unitary. Its sole correctness property concerns the
whole compressed dilation, at the paper's fixed accuracy. Selected-block and
final probability estimates are derived below, not fields of this record. -/
structure GenericFullFilterImplementation (ell s c r T : ℕ)
    (C : ℕ → KrausChannel (WorkSpace s × Bits c)) where
  matrix : Matrix (FilterSpace ell s c r) (FilterSpace ell s c r) ℂ
  unitary : OneCleanQubit.Unitary matrix
  full_filter_error :
    ‖implementedFilterBlock matrix - idealFilter
      (sourceHistoryMatrix C T (Fintype.card (Bits ell)))
      (biasLam (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s)))‖ ≤
        biasEps (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s))

/-- Terminal clock state computed from the source's fixed running-time bound. -/
def terminalClock (ell T : ℕ) (hJ : T+1 ≤ Fintype.card (Bits ell)) : Bits ell :=
  (clockIndex ell).symm ⟨T,by omega⟩

/-- F acts on all small registers while leaving every filter auxiliary fixed. -/
def readoutPreparation (ell s r T : ℕ) (hJ : T+1 ≤ Fintype.card (Bits ell)) :
    Matrix (AuxiliarySmall ell s r) (AuxiliarySmall ell s r) ℂ :=
  Matrix.kronecker (1 : Matrix (Bits r) (Bits r) ℂ) (F ell s 0 (terminalClock ell T hJ))

/-- The actual unitary W*=F†Uf used in the one-clean-qubit readout. -/
def readoutUnitary {ell s c r T : ℕ} {C : ℕ → KrausChannel (WorkSpace s × Bits c)}
    (I : GenericFullFilterImplementation ell s c r T C)
    (hJ : T+1 ≤ Fintype.card (Bits ell)) :
    Matrix (FilterSpace ell s c r) (FilterSpace ell s c r) ℂ :=
  (Matrix.kronecker (readoutPreparation ell s r T hJ)
    (1 : Matrix (CatalystData c) (CatalystData c) ℂ)).conjTranspose * I.matrix

lemma readoutUnitary_unitary {ell s c r T : ℕ} {C : ℕ → KrausChannel (WorkSpace s × Bits c)}
    (I : GenericFullFilterImplementation ell s c r T C)
    (hJ : T+1 ≤ Fintype.card (Bits ell)) : OneCleanQubit.Unitary (readoutUnitary I hJ) := by
  have hF := unitary_tensor (1 : Matrix (Bits r) (Bits r) ℂ)
    (F ell s 0 (terminalClock ell T hJ)) unitary_one
    (F_unitary ell s 0 (terminalClock ell T hJ))
  have hFull := unitary_tensor _ (1 : Matrix (CatalystData c) (CatalystData c) ℂ) hF unitary_one
  have hAdj : OneCleanQubit.Unitary
      (Matrix.kronecker (readoutPreparation ell s r T hJ)
        (1 : Matrix (CatalystData c) (CatalystData c) ℂ)).conjTranspose := by
    constructor
    · simpa only [Matrix.conjTranspose_conjTranspose, readoutPreparation] using hFull.2
    · simpa only [Matrix.conjTranspose_conjTranspose, readoutPreparation] using hFull.1
  exact OneCleanQubit.unitary_mul hAdj I.unitary

/-- The actual physical F†Uf zero block, derived from auxiliary compression
and the proved F-preparation columns. -/
lemma readoutUnitary_selected_block {ell s c r T : ℕ}
    {C : ℕ → KrausChannel (WorkSpace s × Bits c)}
    (I : GenericFullFilterImplementation ell s c r T C)
    (hJ : T+1 ≤ Fintype.card (Bits ell)) :
    (readoutUnitary I hJ).submatrix
      (fun j => (ancillaryZero ell s r,j)) (fun j => (ancillaryZero ell s r,j)) =
    physicalReadout ell s ((Fintype.card (Bits c))^2) (terminalClock ell T hJ)
      (implementedFilterBlock I.matrix) := by
  unfold readoutUnitary readoutPreparation ancillaryZero
  rw [auxiliary_readout_compression]
  unfold physicalReadout implementedFilterBlock auxiliaryBlock
  simp only [Matrix.submatrix_submatrix, Function.comp_def, Equiv.symm_apply_apply]

lemma readoutUnitary_selected_amplitude {ell s c r T : ℕ}
    {C : ℕ → KrausChannel (WorkSpace s × Bits c)}
    (I : GenericFullFilterImplementation ell s c r T C)
    (hJ : T+1 ≤ Fintype.card (Bits ell)) :
    normalizedReTrace ((readoutUnitary I hJ).submatrix
      (fun j => (ancillaryZero ell s r,j)) (fun j => (ancillaryZero ell s r,j))) =
    selectedAmplitude hJ (zeroWork s) (implementedFilterBlock I.matrix) := by
  rw [readoutUnitary_selected_block, physicalReadout_eq_selected]
  have hz : (0 : Fin (Fintype.card (Bits ell))) = ⟨0,by omega⟩ := by
    apply Fin.ext
    simp
  simp only [terminalClock, Equiv.apply_symm_apply, clockIndex_zero, selectedAmplitude, hz]

/-- Source acceptance is evaluated by its actual Born output on a fixed
catalyst basis state. Exact restoration makes this value independent of that
choice, as proved by `source_filter_budget`. -/
def sourceProbability {s c : ℕ} (C : ℕ → KrausChannel (WorkSpace s × Bits c)) (T : ℕ) : ℝ :=
  SourceReduction.sourceAccept ((KrausChannel.sequence C 0 T).act
    (Matrix.kronecker (Matrix.single (zeroWork s) (zeroWork s) 1)
      (Matrix.single (zeroBits c) (zeroBits c) 1)))


/-- Number of small mixed-register qubits, including filter auxiliaries,
the clock, selector, and both copies of the work register. -/
def smallQubits (ell s r : ℕ) : ℕ := r + ell + s + s + 3

lemma auxiliarySmall_card (ell s r : ℕ) :
    Fintype.card (AuxiliarySmall ell s r) = 2 ^ smallQubits ell s r := by
  simp [AuxiliarySmall, StatePreparation.Small, WorkSpace, Bits, smallQubits, pow_add]
  <;> ring

lemma mixedTarget_card (ell s c r : ℕ) :
    Fintype.card (FilterSpace ell s c r ⊕ FilterSpace ell s c r) =
      2 ^ (c+c+smallQubits ell s r+1) := by
  simp only [Fintype.card_sum, FilterSpace, Fintype.card_prod, auxiliarySmall_card,
    CatalystData, Fintype.card_fin, Bits, Fintype.card_fun, Fintype.card_fin]
  simp only [smallQubits, pow_add, pow_two]
  ring

/-- The paper's explicit positive gap, with all small qubits accounted for. -/
def targetGap (ell s r : ℕ) : ℝ :=
  biasLam (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s)) /
    ((2 : ℝ) ^ (smallQubits ell s r + 3) * Real.sqrt (Fintype.card (WorkSpace s)))

lemma targetGap_eq_cardinality (ell s r : ℕ) :
    targetGap ell s r =
      biasLam (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s)) /
        (8*(Fintype.card (AuxiliarySmall ell s r) : ℝ)*Real.sqrt (Fintype.card (WorkSpace s))) := by
  rw [targetGap, auxiliarySmall_card]
  push_cast
  rw [pow_add]
  norm_num
  ring

/-- Actual reflected trace unitary, including the additional maximally mixed
bit from Lemma 6. -/
def targetTraceUnitary {ell s c r T : ℕ} {C : ℕ → KrausChannel (WorkSpace s × Bits c)}
    (I : GenericFullFilterImplementation ell s c r T C)
    (hJ : T+1 ≤ Fintype.card (Bits ell)) :
    OneCleanQubit.ProbeMatrix (FilterSpace ell s c r) :=
  OneCleanQubit.reflectedTraceUnitary
    (OneCleanQubit.ancillaryProjector (n := CatalystData c)
      (AuxiliarySmall ell s r) (ancillaryZero ell s r)) (readoutUnitary I hJ)

/-- Born acceptance probability of H controlled(V) H on one clean probe and
an otherwise maximally mixed input. -/
def targetProbability {ell s c r T : ℕ} {C : ℕ → KrausChannel (WorkSpace s × Bits c)}
    (I : GenericFullFilterImplementation ell s c r T C)
    (hJ : T+1 ≤ Fintype.card (Bits ell)) : ℝ :=
  OneCleanQubit.probZero (OneCleanQubit.output (targetTraceUnitary I hJ))

/-- Equation (23) for the actual density-matrix readout, relative only to the
explicit full-filter implementation record. The source supplies its genuine
channels, exact catalyst restoration, and the usual bounded-error acceptance
promise (in the two implications). All intermediate trace-error, selected-
block, restoration-column, and CPTP-norm hypotheses are proved here.

This conditional assembly does not assert that the implementation record has
been constructed by the source-to-filter compiler. -/
theorem source_probability_gap_relative_to_full_filter {ell s c r T : ℕ}
    (C : ℕ → KrausChannel (WorkSpace s × Bits c))
    (hJ : T+1 ≤ Fintype.card (Bits ell))
    (hrestore : ∀ ρ, IsDensity ρ →
      workPartialTrace ((KrausChannel.sequence C 0 T).act
        (Matrix.kronecker (Matrix.single (zeroWork s) (zeroWork s) 1) ρ)) = ρ)
    (I : GenericFullFilterImplementation ell s c r T C) :
    0 < targetGap ell s r ∧
      OneCleanQubit.Unitary (OneCleanQubit.circuit (targetTraceUnitary I hJ)) ∧
      (0 ≤ targetProbability I hJ ∧ targetProbability I hJ ≤ 1) ∧
      (2/3 ≤ sourceProbability C T → 1/2 + targetGap ell s r ≤ targetProbability I hJ) ∧
      (sourceProbability C T ≤ 1/3 → targetProbability I hJ ≤ 1/2 - targetGap ell s r) := by
  classical
  letI : Nonempty (AuxiliarySmall ell s r) := ⟨ancillaryZero ell s r⟩
  obtain ⟨η,hη,haccept,herror⟩ := source_filter_budget C (zeroWork s) (zeroBits c)
    T (Fintype.card (Bits ell)) hJ hrestore
  have hσ : Matrix.trace (Matrix.single (zeroBits c) (zeroBits c) (1 : ℂ)) = 1 := by
    simp [Matrix.trace, Matrix.single]
  have hp : sourceProbability C T = SourceBias.accept η :=
    haccept (Matrix.single (zeroBits c) (zeroBits c) 1) hσ
  have herr := herror (implementedFilterBlock I.matrix) I.full_filter_error
  rw [← hp] at herr
  have herr' : |normalizedReTrace ((readoutUnitary I hJ).submatrix
        (fun j => (ancillaryZero ell s r,j)) (fun j => (ancillaryZero ell s r,j))) -
      biasLam (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s)) *
        (2*sourceProbability C T-1) / Real.sqrt (Fintype.card (WorkSpace s))| ≤
      biasLam (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s)) /
        (100*(Fintype.card (WorkSpace s) : ℝ)) := by
    rw [readoutUnitary_selected_amplitude]
    exact herr
  have hJone : (1 : ℝ) ≤ Fintype.card (Bits ell) := by
    exact_mod_cast (show 1 ≤ Fintype.card (Bits ell) by omega)
  have hKone : (1 : ℝ) ≤ Fintype.card (WorkSpace s) := by
    exact_mod_cast (Fintype.card_pos_iff.mpr ⟨zeroWork s⟩)
  have hlam := biasLam_pos (lt_of_lt_of_le zero_lt_one hJone)
    (lt_of_lt_of_le zero_lt_one hKone)
  have hW := readoutUnitary_unitary I hJ
  have hV : OneCleanQubit.Unitary (targetTraceUnitary I hJ) :=
    OneCleanQubit.reflectedTraceUnitary_unitary _ _
      (OneCleanQubit.ancillaryProjector_hermitian _ _)
      (OneCleanQubit.ancillaryProjector_idempotent _ _) hW
  have hprob := OneCleanQubit.output_probabilities (targetTraceUnitary I hJ) hV
  have hgap := operational_cardinality_gap (ancillaryZero ell s r) (readoutUnitary I hJ) hW
    (biasLam (Fintype.card (Bits ell)) (Fintype.card (WorkSpace s)))
    (Fintype.card (WorkSpace s)) (sourceProbability C T) hlam hKone herr'
  have hpositive : 0 < targetGap ell s r := by
    unfold targetGap
    exact div_pos hlam (mul_pos (by positivity)
      (Real.sqrt_pos.mpr (lt_of_lt_of_le zero_lt_one hKone)))
  refine ⟨hpositive,OneCleanQubit.circuit_unitary _ hV,⟨hprob.1,hprob.2.1⟩,?_⟩
  simpa only [targetGap_eq_cardinality, targetProbability, targetTraceUnitary] using hgap

end Paper25.SourceSimulation
