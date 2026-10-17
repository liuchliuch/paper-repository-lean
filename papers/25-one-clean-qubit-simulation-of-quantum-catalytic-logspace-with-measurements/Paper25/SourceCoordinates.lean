import Paper25.SourceReduction
import Paper25.ElementarySourceExpansion
import Paper25.SourceSimulation

/-!
# From the effective physical source model to the catalytic reduction

The designated output wire is separated from the remaining work wires. Inputs,
Born acceptance, exact marginal restoration and the real expanded channel
schedule are transported through this explicit computational coordinate map.
-/
noncomputable section
open Matrix
open scoped ComplexOrder ComplexConjugate
open Paper25.OperationalModel
namespace Paper25.SourceCoordinates

set_option maxHeartbeats 800000
set_option synthInstance.maxSize 512
attribute [local instance] Classical.propDecidable

abbrev Remaining (s : ℕ) (o : Fin s) := {j : Fin s // j ≠ o} → OperationalModel.Bit

instance remainingDecidableEq (s : ℕ) (o : Fin s) : DecidableEq (Remaining s o) :=
  Fintype.decidablePiFintype

/-- Read the chosen output bit and all other work positions. -/
def workOutputIndex (s : ℕ) (o : Fin s) : Basis s ≃ SourceBias.Work (Remaining s o) where
  toFun f := (f o,fun j => f j.1)
  invFun p := fun j => if h : j=o then p.1 else p.2 ⟨j,h⟩
  left_inv f := by
    funext j
    by_cases h : j=o
    · subst j; simp
    · simp [h]
  right_inv p := by
    apply Prod.ext
    · simp
    · funext j; simp [j.2]

@[simp] lemma workOutputIndex_output (s : ℕ) (o : Fin s) (f : Basis s) :
    (workOutputIndex s o f).1 = f o := rfl

@[simp] lemma workOutputIndex_zero (s : ℕ) (o : Fin s) :
    workOutputIndex s o (fun _ => 0) = (0,fun _ => 0) := rfl

lemma workOutputIndex_card (s : ℕ) (o : Fin s) :
    Fintype.card (SourceBias.Work (Remaining s o)) = 2^s := by
  rw [← Fintype.card_congr (workOutputIndex s o),card_basis]

variable {G : EffectiveGateSet}

abbrev Rem (C : EffectiveSourceComputation G) := Remaining C.workQubits C.outputQubit
abbrev Work (C : EffectiveSourceComputation G) := SourceBias.Work (Rem C)
abbrev Cat (C : EffectiveSourceComputation G) := Basis C.catalystQubits

def cleanIndex (C : EffectiveSourceComputation G) : Work C := (0,fun _ => 0)

/-- The physical work/catalyst split followed only by the output-wire separation. -/
def fullIndex (C : EffectiveSourceComputation G) :
    Basis (C.workQubits+C.catalystQubits) ≃ (Work C × Cat C) :=
  (registerBasis C.workQubits C.catalystQubits).trans
    ((workOutputIndex C.workQubits C.outputQubit).prodCongr (Equiv.refl _))

@[simp] lemma fullIndex_output (C : EffectiveSourceComputation G)
    (f : Basis (C.workQubits+C.catalystQubits)) :
    (fullIndex C f).1.1 = f (Fin.castAdd C.catalystQubits C.outputQubit) := rfl

@[simp] lemma fullIndex_symm_output (C : EffectiveSourceComputation G) (p : Work C × Cat C) :
    (fullIndex C).symm p (Fin.castAdd C.catalystQubits C.outputQubit) = p.1.1 := by
  have h := congrArg (fun z : Work C × Cat C => z.1.1) ((fullIndex C).apply_symm_apply p)
  exact h

lemma pureZero_coordinates (s : ℕ) (o : Fin s) :
    (pureZero s).submatrix (workOutputIndex s o).symm (workOutputIndex s o).symm =
      Matrix.single (0,fun _ => 0) (0,fun _ => 0) (1 : ℂ) := by
  ext i j
  have heq (w : SourceBias.Work (Remaining s o)) :
      (workOutputIndex s o).symm w = (fun _ => 0) ↔ w = (0,fun _ => 0) := by
    rw [Equiv.symm_apply_eq]
    rfl
  simp [pureZero,Matrix.single,Matrix.submatrix_apply,heq,eq_comm]

/-- The actual source input becomes the clean-work matrix unit tensored with σ. -/
theorem input_coordinates (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    (C.input σ).submatrix (fullIndex C).symm (fullIndex C).symm =
      Matrix.kronecker (Matrix.single (cleanIndex C) (cleanIndex C) 1) σ := by
  ext ⟨w,v⟩ ⟨w',v'⟩
  have h := congrArg (fun M => M w w') (pureZero_coordinates C.workQubits C.outputQubit)
  simpa [EffectiveSourceComputation.input,fullIndex,cleanIndex,Matrix.submatrix_apply,
    Matrix.kronecker,Matrix.kroneckerMap_apply] using congrArg (fun z : ℂ => z * σ v v') h

/-- The actual channel in the reduction's work/catalyst coordinates. -/
def sourceChannel (C : EffectiveSourceComputation G) : KrausChannel (Work C × Cat C) :=
  relabelChannel (fullIndex C).symm C.gates.channel

def sourceOutput (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    Matrix (Work C × Cat C) (Work C × Cat C) ℂ :=
  (sourceChannel C).act (Matrix.kronecker (Matrix.single (cleanIndex C) (cleanIndex C) 1) σ)

lemma sourceOutput_coordinates (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    sourceOutput C σ = (C.output σ).submatrix (fullIndex C).symm (fullIndex C).symm := by
  rw [sourceOutput,←input_coordinates]
  exact relabelChannel_act (fullIndex C).symm C.gates.channel (C.input σ)

/-- Actual source Born acceptance is exactly the reduction's sourceAccept. -/
theorem accept_coordinates (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    C.accept σ = SourceReduction.sourceAccept (sourceOutput C σ) := by
  let f : Basis (C.workQubits+C.catalystQubits) → ℝ := fun b =>
    if b (Fin.castAdd C.catalystQubits C.outputQubit) = 1 then (C.output σ b b).re else 0
  change (∑ b, f b) = _
  rw [← (fullIndex C).symm.sum_comp f,sourceOutput_coordinates]
  dsimp only [f]
  simp only [fullIndex_symm_output,Matrix.submatrix_apply,SourceReduction.sourceAccept,
    Fintype.sum_prod_type,Fin.sum_univ_two]
  simp [Complex.re_sum]

/-- Forget a one-dimensional reference without changing any quantum coordinate. -/
def unitIndex (a : Type*) : (a × Unit) ≃ a where
  toFun p := p.1
  invFun x := (x,())
  left_inv p := by rcases p with ⟨x,⟨⟩⟩; rfl
  right_inv x := rfl

def referenceUnitInput (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    Matrix (Basis (C.workQubits+C.catalystQubits) × Unit)
      (Basis (C.workQubits+C.catalystQubits) × Unit) ℂ :=
  (Matrix.kronecker (pureZero C.workQubits)
    (σ.submatrix (unitIndex (Cat C)) (unitIndex (Cat C)))).submatrix
      (C.referenceBasis Unit) (C.referenceBasis Unit)

lemma referenceUnitInput_eq (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    referenceUnitInput C σ = (C.input σ).submatrix
      (unitIndex (Basis (C.workQubits+C.catalystQubits)))
      (unitIndex (Basis (C.workQubits+C.catalystQubits))) := by
  ext ⟨i,⟨⟩⟩ ⟨j,⟨⟩⟩
  rfl

lemma referenceUnitOutput_eq (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    (C.gates.channel.extendRight Unit).act (referenceUnitInput C σ) =
      (C.output σ).submatrix (unitIndex (Basis (C.workQubits+C.catalystQubits)))
        (unitIndex (Basis (C.workQubits+C.catalystQubits))) := by
  ext ⟨i,⟨⟩⟩ ⟨j,⟨⟩⟩
  rw [referenceUnitInput_eq,KrausChannel.extendRight_act_block]
  rfl

/-- Full restoration from the physical model in particular implies the ordinary
catalyst marginal condition used by Lemma 2 and SourceReduction. -/
theorem restores_marginal (C : EffectiveSourceComputation G) (hr : C.Restores)
    (σ : Operator C.catalystQubits) (hσ : IsDensity σ) :
    workPartialTrace (sourceOutput C σ) = σ := by
  have hσU : (σ.submatrix (unitIndex (Cat C)) (unitIndex (Cat C))).PosSemidef :=
    hσ.1.submatrix _
  have htU : Matrix.trace (σ.submatrix (unitIndex (Cat C)) (unitIndex (Cat C))) = 1 := by
    rw [trace_submatrix_equiv,hσ.2]
  have hrest := hr Unit (σ.submatrix (unitIndex (Cat C)) (unitIndex (Cat C))) hσU htU
  ext v v'
  have h := hrest (v,()) (v',())
  change (∑ w, (C.gates.channel.extendRight Unit).act (referenceUnitInput C σ)
      ((C.referenceBasis Unit).symm (w,(v,())))
      ((C.referenceBasis Unit).symm (w,(v',())))) = σ v v' at h
  rw [referenceUnitOutput_eq] at h
  change (∑ w, C.output σ
      ((registerBasis C.workQubits C.catalystQubits).symm (w,v))
      ((registerBasis C.workQubits C.catalystQubits).symm (w,v'))) = σ v v' at h
  rw [sourceOutput_coordinates]
  change (∑ w : Work C, C.output σ
      ((registerBasis C.workQubits C.catalystQubits).symm
        ((workOutputIndex C.workQubits C.outputQubit).symm w,v))
      ((registerBasis C.workQubits C.catalystQubits).symm
        ((workOutputIndex C.workQubits C.outputQubit).symm w,v'))) = σ v v'
  rw [(workOutputIndex C.workQubits C.outputQubit).symm.sum_comp
    (fun w => C.output σ ((registerBasis C.workQubits C.catalystQubits).symm (w,v))
      ((registerBasis C.workQubits C.catalystQubits).symm (w,v')))]
  exact h

/-- Real reset/CNOT/dephase expansion of every retained measurement macro. -/
def expanded (C : EffectiveSourceComputation G) :=
  ElementaryEncoding.expandEffectiveSourceCircuit C.gates

def duration (C : EffectiveSourceComputation G) : ℕ := (expanded C).length

/-- Each history step is the actual primitive channel in the reduction coordinates. -/
def steps (C : EffectiveSourceComputation G) (t : ℕ) : KrausChannel (Work C × Cat C) :=
  relabelChannel (fullIndex C).symm (ElementaryEncoding.primitiveChannelAt (expanded C) t)

lemma relabel_sequence_act {a b : Type*} [Fintype a] [Fintype b]
    [DecidableEq a] [DecidableEq b] (e : a ≃ b) (D : ℕ → KrausChannel b)
    (start len : ℕ) (X : Matrix b b ℂ) :
    (KrausChannel.sequence (fun t => relabelChannel e (D t)) start len).act
      (X.submatrix e e) =
        ((KrausChannel.sequence D start len).act X).submatrix e e := by
  induction len with
  | zero => simp [KrausChannel.sequence]
  | succ len ih =>
    rw [KrausChannel.sequence,KrausChannel.comp_act,ih,relabelChannel_act,
      KrausChannel.sequence,KrausChannel.comp_act]

/-- Equality of full operator semantics, with no restriction to reachable states. -/
theorem expanded_sequence_act (C : EffectiveSourceComputation G)
    (X : Operator (C.workQubits+C.catalystQubits)) :
    (KrausChannel.sequence (steps C) 0 (duration C)).act
      (X.submatrix (fullIndex C).symm (fullIndex C).symm) =
        (C.gates.channel.act X).submatrix (fullIndex C).symm (fullIndex C).symm := by
  unfold steps
  rw [relabel_sequence_act]
  exact congrArg (fun M => M.submatrix (fullIndex C).symm (fullIndex C).symm)
    (ElementaryEncoding.expandedEffectiveSequence_act C.gates X)

theorem steps_input_output (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    (KrausChannel.sequence (steps C) 0 (duration C)).act
      (Matrix.kronecker (Matrix.single (cleanIndex C) (cleanIndex C) 1) σ) = sourceOutput C σ := by
  rw [←input_coordinates,sourceOutput_coordinates]
  exact expanded_sequence_act C (C.input σ)

/-- This is exactly the restoration input expected by source_history_reduction. -/
theorem steps_restores (C : EffectiveSourceComputation G) (hr : C.Restores) :
    ∀ σ : Matrix (Cat C) (Cat C) ℂ, IsDensity σ →
      workPartialTrace ((KrausChannel.sequence (steps C) 0 (duration C)).act
        (Matrix.kronecker (Matrix.single (cleanIndex C) (cleanIndex C) 1) σ)) = σ := by
  intro σ hσ
  rw [steps_input_output]
  exact restores_marginal C hr σ hσ

/-- Reduction acceptance is the actual physical acceptance even after macro expansion. -/
theorem steps_accept (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    SourceReduction.sourceAccept ((KrausChannel.sequence (steps C) 0 (duration C)).act
      (Matrix.kronecker (Matrix.single (cleanIndex C) (cleanIndex C) 1) σ)) = C.accept σ := by
  rw [steps_input_output,accept_coordinates]

lemma duration_le (C : EffectiveSourceComputation G) : duration C ≤ 3*C.gates.length :=
  ElementaryEncoding.expandEffectiveSourceCircuit_length C.gates

lemma work_card (C : EffectiveSourceComputation G) : Fintype.card (Work C) = 2^C.workQubits :=
  workOutputIndex_card C.workQubits C.outputQubit

lemma catalyst_card (C : EffectiveSourceComputation G) : Fintype.card (Cat C) = 2^C.catalystQubits :=
  card_basis C.catalystQubits

/-- The raw doubled physical coordinates for the work/catalyst-ordered history. -/
def rawOperatorIndex (C : EffectiveSourceComputation G) :
    (Fin ((Fintype.card (Work C))^2) × Fin ((Fintype.card (Cat C))^2)) ≃
      (Basis (C.workQubits+C.catalystQubits) × Basis (C.workQubits+C.catalystQubits)) :=
  (((SourceBias.operatorIndex (Work C)).prodCongr (SourceBias.operatorIndex (Cat C))).trans
    (reshuffleEquiv (α := Work C) (β := Work C) (γ := Cat C) (δ := Cat C))).trans
      ((fullIndex C).symm.prodCongr (fullIndex C).symm)

lemma coordinates_eq_raw (C : EffectiveSourceComputation G) (t : ℕ) :
    SourceReduction.coordinates (steps C) t =
      (ElementaryEncoding.primitiveChannelAt (expanded C) t).liouville.submatrix
        (rawOperatorIndex C) (rawOperatorIndex C) := by
  rw [SourceReduction.coordinates,steps,sourceLiouville_eq_submatrix,
    ElementaryEncoding.relabel_liouville]
  rfl

/-- The actual eight local-unitary terms encode the history matrices consumed
by the source reduction, with every coordinate map fixed above. -/
theorem coordinates_eight_term_average (C : EffectiveSourceComputation G) (t : ℕ) :
    (1 / 8 : ℂ) • ∑ j, ElementaryEncoding.primitiveTermsAt (expanded C) (rawOperatorIndex C) t j =
      (1 / 2 : ℂ) • SourceReduction.coordinates (steps C) t := by
  rw [coordinates_eq_raw]
  exact ElementaryEncoding.primitiveTermsAt_average _ _ _


/-- Number of work positions other than the designated output position. -/
def restQubits (C : EffectiveSourceComputation G) : ℕ :=
  Fintype.card {j : Fin C.workQubits // j ≠ C.outputQubit}

lemma restQubits_add_one (C : EffectiveSourceComputation G) :
    restQubits C + 1 = C.workQubits := by
  have hp : 0 < C.workQubits := Nat.zero_lt_of_lt C.outputQubit.isLt
  have hc : restQubits C = C.workQubits - 1 := by
    unfold restQubits
    rw [Fintype.card_subtype_compl]
    simp
  omega

/-- An enumeration of remaining physical positions, not of Hilbert basis states. -/
def otherPositions (C : EffectiveSourceComputation G) :
    Fin (restQubits C) ≃ {j : Fin C.workQubits // j ≠ C.outputQubit} :=
  let e : Fin (restQubits C + 1) ≃ Fin C.workQubits := finCongr (restQubits_add_one C)
  (finSuccAboveEquiv (e.symm C.outputQubit)).trans
    (e.subtypeEquiv (fun j => by
      constructor
      · intro hj he
        apply hj
        apply e.injective
        exact he.trans (e.apply_symm_apply C.outputQubit).symm
      · intro hj he
        apply hj
        rw [he,e.apply_symm_apply]))

/-- The position enumeration is the explicit skip-output arithmetic map. -/
lemma otherPositions_val (C : EffectiveSourceComputation G) (i : Fin (restQubits C)) :
    (otherPositions C i).1.val =
      if i.val < C.outputQubit.val then i.val else i.val+1 := by
  simp [otherPositions,finSuccAboveEquiv_apply,Equiv.subtypeEquiv,Fin.succAbove,
    Fin.lt_def,apply_ite]

/-- The canonical bit register is obtained by precomposition with the physical
position enumeration. Thus no arbitrary computational-basis permutation is used. -/
def remainingIndex (C : EffectiveSourceComputation G) :
    Rem C ≃ StatePreparation.Bits (restQubits C) where
  toFun f i := f (otherPositions C i)
  invFun f j := f ((otherPositions C).symm j)
  left_inv f := by funext j; simp
  right_inv f := by funext j; simp

@[simp] lemma remainingIndex_zero (C : EffectiveSourceComputation G) :
    remainingIndex C (fun _ => 0) = StatePreparation.zeroBits (restQubits C) := rfl

def workCanonicalIndex (C : EffectiveSourceComputation G) :
    Work C ≃ StatePreparation.WorkSpace (restQubits C) :=
  (Equiv.refl OperationalModel.Bit).prodCongr (remainingIndex C)

@[simp] lemma workCanonicalIndex_clean (C : EffectiveSourceComputation G) :
    workCanonicalIndex C (cleanIndex C) = StatePreparation.zeroWork (restQubits C) := rfl

/-- All canonical coordinates are induced by work and catalyst wire positions. -/
def canonicalIndex (C : EffectiveSourceComputation G) :
    Basis (C.workQubits+C.catalystQubits) ≃
      (StatePreparation.WorkSpace (restQubits C) × StatePreparation.Bits C.catalystQubits) :=
  (fullIndex C).trans ((workCanonicalIndex C).prodCongr (Equiv.refl _))

lemma canonicalIndex_work_bit (C : EffectiveSourceComputation G)
    (f : Basis (C.workQubits+C.catalystQubits)) (i : Fin (restQubits C)) :
    (canonicalIndex C f).1.2 i =
      f (Fin.castAdd C.catalystQubits (otherPositions C i).1) := rfl

@[simp] lemma canonicalIndex_output (C : EffectiveSourceComputation G)
    (f : Basis (C.workQubits+C.catalystQubits)) :
    (canonicalIndex C f).1.1 = f (Fin.castAdd C.catalystQubits C.outputQubit) := rfl

lemma canonicalIndex_catalyst_bit (C : EffectiveSourceComputation G)
    (f : Basis (C.workQubits+C.catalystQubits)) (i : Fin C.catalystQubits) :
    (canonicalIndex C f).2 i = f (Fin.natAdd C.workQubits i) := rfl

lemma canonical_input (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    (C.input σ).submatrix (canonicalIndex C).symm (canonicalIndex C).symm =
      Matrix.kronecker
        (Matrix.single (StatePreparation.zeroWork (restQubits C))
          (StatePreparation.zeroWork (restQubits C)) 1) σ := by
  have h := congrArg (fun M => M.submatrix
    ((workCanonicalIndex C).symm.prodCongr (Equiv.refl (Cat C)))
    ((workCanonicalIndex C).symm.prodCongr (Equiv.refl (Cat C)))) (input_coordinates C σ)
  have heq (w : StatePreparation.WorkSpace (restQubits C)) :
      (workCanonicalIndex C).symm w = cleanIndex C ↔
        w = StatePreparation.zeroWork (restQubits C) := by
    rw [Equiv.symm_apply_eq,workCanonicalIndex_clean]
  ext ⟨w,v⟩ ⟨w',v'⟩
  have he := congrArg (fun M => M (w,v) (w',v')) h
  simpa [canonicalIndex,Matrix.submatrix_apply,Matrix.kronecker,
    Matrix.kroneckerMap_apply,Matrix.single,heq,eq_comm] using he

/-- The canonical sequence still executes the actual expanded source operations. -/
def canonicalSteps (C : EffectiveSourceComputation G) (t : ℕ) :
    KrausChannel (StatePreparation.WorkSpace (restQubits C) ×
      StatePreparation.Bits C.catalystQubits) :=
  relabelChannel (canonicalIndex C).symm (ElementaryEncoding.primitiveChannelAt (expanded C) t)

def canonicalOutput (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :=
  (C.output σ).submatrix (canonicalIndex C).symm (canonicalIndex C).symm

lemma canonicalOutput_reindex (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    canonicalOutput C σ = (sourceOutput C σ).submatrix
      ((workCanonicalIndex C).symm.prodCongr (Equiv.refl (Cat C)))
      ((workCanonicalIndex C).symm.prodCongr (Equiv.refl (Cat C))) := by
  rw [sourceOutput_coordinates]
  rfl

theorem canonical_steps_input_output (C : EffectiveSourceComputation G)
    (σ : Operator C.catalystQubits) :
    (KrausChannel.sequence (canonicalSteps C) 0 (duration C)).act
      (Matrix.kronecker
        (Matrix.single (StatePreparation.zeroWork (restQubits C))
          (StatePreparation.zeroWork (restQubits C)) 1) σ) = canonicalOutput C σ := by
  rw [←canonical_input]
  unfold canonicalSteps
  rw [relabel_sequence_act]
  exact congrArg (fun M => M.submatrix (canonicalIndex C).symm (canonicalIndex C).symm)
    (ElementaryEncoding.expandedEffectiveSequence_act C.gates (C.input σ))

/-- Canonical acceptance is the original Born probability on the chosen output wire. -/
theorem canonical_accept (C : EffectiveSourceComputation G) (σ : Operator C.catalystQubits) :
    SourceReduction.sourceAccept (canonicalOutput C σ) = C.accept σ := by
  rw [accept_coordinates,canonicalOutput_reindex]
  unfold SourceReduction.sourceAccept
  congr 1
  exact (remainingIndex C).symm.sum_comp
    (fun a => ∑ v, sourceOutput C σ ((1,a),v) ((1,a),v))

/-- Full physical reference restoration supplies the canonical restoration premise. -/
theorem canonical_steps_restores (C : EffectiveSourceComputation G) (hr : C.Restores) :
    ∀ σ : Matrix (StatePreparation.Bits C.catalystQubits)
      (StatePreparation.Bits C.catalystQubits) ℂ, IsDensity σ →
      workPartialTrace ((KrausChannel.sequence (canonicalSteps C) 0 (duration C)).act
        (Matrix.kronecker
          (Matrix.single (StatePreparation.zeroWork (restQubits C))
            (StatePreparation.zeroWork (restQubits C)) 1) σ)) = σ := by
  intro σ hσ
  rw [canonical_steps_input_output,canonicalOutput_reindex]
  ext v v'
  change (∑ w, sourceOutput C σ ((workCanonicalIndex C).symm w,v)
    ((workCanonicalIndex C).symm w,v')) = σ v v'
  rw [(workCanonicalIndex C).symm.sum_comp
    (fun w => sourceOutput C σ (w,v) (w,v'))]
  exact congrArg (fun M => M v v') (restores_marginal C hr σ hσ)

theorem canonical_steps_accept (C : EffectiveSourceComputation G)
    (σ : Operator C.catalystQubits) :
    SourceReduction.sourceAccept ((KrausChannel.sequence (canonicalSteps C) 0 (duration C)).act
      (Matrix.kronecker
        (Matrix.single (StatePreparation.zeroWork (restQubits C))
          (StatePreparation.zeroWork (restQubits C)) 1) σ)) = C.accept σ := by
  rw [canonical_steps_input_output,canonical_accept]

/-- In the actual-filter theorem the chosen catalyst input is precisely this
basis density; its reported source probability is the physical source Born value. -/
theorem canonical_sourceProbability (C : EffectiveSourceComputation G) :
    SourceSimulation.sourceProbability (canonicalSteps C) (duration C) =
      C.accept (Matrix.single (StatePreparation.zeroBits C.catalystQubits)
        (StatePreparation.zeroBits C.catalystQubits) 1) :=
  canonical_steps_accept C _

/-- All raw doubled source coordinates after the physical wire reindexing and
Liouville reshuffle required by the history LCU. -/
def canonicalRawOperatorIndex (C : EffectiveSourceComputation G) :
    (Fin ((Fintype.card (StatePreparation.WorkSpace (restQubits C)))^2) ×
      SourceSimulation.CatalystData C.catalystQubits) ≃
      (Basis (C.workQubits+C.catalystQubits) × Basis (C.workQubits+C.catalystQubits)) :=
  (((SourceBias.operatorIndex (StatePreparation.WorkSpace (restQubits C))).prodCongr
    (SourceBias.operatorIndex (StatePreparation.Bits C.catalystQubits))).trans
    (reshuffleEquiv (α := StatePreparation.WorkSpace (restQubits C))
      (β := StatePreparation.WorkSpace (restQubits C))
      (γ := StatePreparation.Bits C.catalystQubits)
      (δ := StatePreparation.Bits C.catalystQubits))).trans
      ((canonicalIndex C).symm.prodCongr (canonicalIndex C).symm)

lemma canonical_coordinates_eq_raw (C : EffectiveSourceComputation G) (t : ℕ) :
    SourceReduction.coordinates (canonicalSteps C) t =
      (ElementaryEncoding.primitiveChannelAt (expanded C) t).liouville.submatrix
        (canonicalRawOperatorIndex C) (canonicalRawOperatorIndex C) := by
  rw [SourceReduction.coordinates,canonicalSteps,sourceLiouville_eq_submatrix,
    ElementaryEncoding.relabel_liouville]
  rfl

/-- Concrete K for the final filter theorem, obtained from each actual primitive's
proved eight-unitary encoding; no LCU witness is supplied by a caller. -/
def canonicalK (C : EffectiveSourceComputation G) (t : ℕ) (j : Fin 8) :
    Matrix
      (Fin ((Fintype.card (StatePreparation.WorkSpace (restQubits C)))^2) ×
        SourceSimulation.CatalystData C.catalystQubits)
      (Fin ((Fintype.card (StatePreparation.WorkSpace (restQubits C)))^2) ×
        SourceSimulation.CatalystData C.catalystQubits) ℂ :=
  ElementaryEncoding.primitiveTermsAt (expanded C) (canonicalRawOperatorIndex C) t j

theorem canonicalK_unitary (C : EffectiveSourceComputation G) (t : ℕ) (j : Fin 8) :
    canonicalK C t j ∈ Matrix.unitaryGroup
      (Fin ((Fintype.card (StatePreparation.WorkSpace (restQubits C)))^2) ×
        SourceSimulation.CatalystData C.catalystQubits) ℂ :=
  ElementaryEncoding.primitiveTermsAt_unitary _ _ _ _

theorem canonicalK_average (C : EffectiveSourceComputation G) (t : ℕ) :
    (1 / 8 : ℂ) • ∑ j, canonicalK C t j =
      (1 / 2 : ℂ) • SourceReduction.coordinates (canonicalSteps C) t := by
  rw [canonical_coordinates_eq_raw]
  exact ElementaryEncoding.primitiveTermsAt_average _ _ _

end Paper25.SourceCoordinates
