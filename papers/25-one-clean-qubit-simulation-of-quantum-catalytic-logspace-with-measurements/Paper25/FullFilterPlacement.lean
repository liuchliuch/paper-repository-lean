import Paper25.CoherentCompilation
import Paper25.SourceWalkCompilation
import Paper25.SourcePreparationPlacement
import Paper25.SourceCircuitSimulation
import Paper25.FullPrecisionBudget
import Paper25.SourceDataReadback

/-! The actual source walk, raw numerical label rotations and QFT network are
assembled into a full native filter. Every register map is the explicit wire
layout of the source compiler or the physical preparation, never a supplied
whole-register basis permutation. -/
noncomputable section
open Matrix
open scoped Matrix.Norms.L2Operator
namespace Paper25.FullFilterPlacement
open OperationalModel OperationalModel.LocalCompilation OperationalModel.CoherentCompilation
open StatePreparation SourceCoordinates SourceTermCompilation SourceHistoryCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 1200000
set_option synthInstance.maxSize 512
variable {G : EffectiveGateSet}

def walkWire (S : EffectiveSourceComputation G) (ell : ℕ) :
    Fin ((4+(ell+DataQubits S))+1) ≃ Fin (SourcePreparationPlacement.walkQubits S ell) :=
  finCongr (by unfold SourcePreparationPlacement.walkQubits SourcePreparationPlacement.encoderQubits DataQubits; omega)

/-- This is a value-preserving relabeling of physical positions. -/
def nativeWalk (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell : ℕ) (prepare : EffectiveCircuit G 1) :
    EffectiveCircuit G (SourcePreparationPlacement.walkQubits S ell) :=
  rewireCircuit (walkWire S ell) (SourceWalkCompilation.circuit conv S ell prepare)

def walkDataLayout (S : EffectiveSourceComputation G) (ell : ℕ) :=
  (rewireBasis (walkWire S ell)).trans (SourceWalkCompilation.walkLayout S ell)

def walkTarget (S : EffectiveSourceComputation G) (ell : ℕ) :
    Operator (SourcePreparationPlacement.walkQubits S ell) :=
  (SelectedFilter.blockWalk (SourceWalkCompilation.idealEncoder S ell) (0,zeroSelector3)).submatrix
    (walkDataLayout S ell) (walkDataLayout S ell)

lemma walkTarget_unitary (S : EffectiveSourceComputation G) (ell : ℕ) :
    walkTarget S ell ∈ Matrix.unitaryGroup _ ℂ := by
  exact unitary_reindex_matrix (rewireBasis (walkWire S ell)) (SourceWalkCompilation.idealWalk S ell)
    (SourceWalkCompilation.idealWalk_unitary S ell)

lemma nativeWalk_error (conv : GateConvention G) (S : EffectiveSourceComputation G)
    (ell : ℕ) (prepare : EffectiveCircuit G 1) (τ : ℝ)
    (hprepare : ‖prepare.matrix-prepareThird.submatrix oneBit oneBit‖ ≤ τ) :
    ‖(nativeWalk conv S ell prepare).matrix-walkTarget S ell‖ ≤ 2*τ := by
  rw [nativeWalk, rewireCircuit_matrix]
  have h := SourceWalkCompilation.circuit_error conv S ell prepare τ hprepare
  rw [← MatrixCompilationNorm.submatrix_equiv_error (rewireBasis (walkWire S ell))] at h
  exact h

/-- Coherent-filter coordinates after interpreting all source data wires. -/
def paperFilterLayout (S : EffectiveSourceComputation G) (ell m : ℕ) :=
  (filterIndex m (SourcePreparationPlacement.walkQubits S ell)).trans
    (Equiv.sumCongr ((Equiv.refl (Fin (2^m))).prodCongr (walkDataLayout S ell))
      ((Equiv.refl (Fin (2^m))).prodCongr (walkDataLayout S ell)))

/-- Raw input width computed by explicit rational arithmetic. -/
def sourceDeltaRaw (S : EffectiveSourceComputation G) (ell : ℕ) : RationalRep :=
  FullPrecisionBudget.deltaRep (Fintype.card (Bits ell))
    (Fintype.card (WorkSpace (restQubits S)))
    (Fintype.card_pos_iff.mpr ⟨zeroBits ell⟩)
    (Fintype.card_pos_iff.mpr ⟨zeroWork _⟩)

lemma sourceDeltaRaw_value (S : EffectiveSourceComputation G) (ell : ℕ) :
    ((sourceDeltaRaw S ell).value : ℝ) =
      biasDelta (Fintype.card (Bits ell)) (Fintype.card (WorkSpace (restQubits S))) :=
  FullPrecisionBudget.deltaRep_value _ _ _ _

lemma sourceDeltaRaw_pos (S : EffectiveSourceComputation G) (ell : ℕ) :
    0 < (sourceDeltaRaw S ell).value := by
  have hJ : 0 < Fintype.card (Bits ell) := Fintype.card_pos_iff.mpr ⟨zeroBits ell⟩
  have hW : 0 < Fintype.card (WorkSpace (restQubits S)) := Fintype.card_pos_iff.mpr ⟨zeroWork _⟩
  dsimp [sourceDeltaRaw, FullPrecisionBudget.deltaRep, FullPrecisionBudget.deltaDen, RationalRep.value]
  positivity

/-- Actual source-dependent native filter, with its actual numerical PREPARE. -/
def nativeUF (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (S : EffectiveSourceComputation G) (ell m precision selectorPrecision n k : ℕ) :
    EffectiveCircuit G (m+(1+SourcePreparationPlacement.walkQubits S ell)) :=
  compiledFilter conv E precision m
    (nativeWalk conv S ell (conv.rotationRep (selectorAngle E selectorPrecision)))
    (sourceDeltaRaw S ell) n k

/-- Native source filter error with every walk and selector premise discharged
by its actual branch circuits. The remaining bounds are numerical precision
budgets, not assumed filter-matrix approximations. -/
theorem nativeUF_error_paper (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : FourierCompilation.StandardQFTCorrectness)
    (S : EffectiveSourceComputation G) (ell m precision selectorPrecision n k : ℕ)
    (σ : ℝ) (hσ : 0 ≤ σ)
    (hk : bitError k ≤ σ/4)
    (hn : bitError n ≤ ((sourceDeltaRaw S ell).value:ℝ)*σ/40) :
    ‖(nativeUF conv E S ell m precision selectorPrecision n k).matrix -
      (coherentWalkFilter (SelectedFilter.blockWalk (SourceWalkCompilation.idealEncoder S ell)
        (0,zeroSelector3)) (2^m)
        (biasDelta (Fintype.card (Bits ell)) (Fintype.card (WorkSpace (restQubits S))))).submatrix
          (paperFilterLayout S ell m) (paperFilterLayout S ell m)‖ ≤
      24*(2^m:ℕ)*bitError selectorPrecision +
        16*(m*(m+2):ℕ)*bitError precision + σ := by
  have hp : ‖(conv.rotationRep (selectorAngle E selectorPrecision)).matrix-
      prepareThird.submatrix oneBit oneBit‖ ≤ 6*bitError selectorPrecision := by
    rw [conv.rotationRep_matrix]
    exact selectorAngle_rotation_error E selectorPrecision
  have hw := nativeWalk_error conv S ell _ (6*bitError selectorPrecision) hp
  have h := compiledFilter_error conv E standard precision m
    (nativeWalk conv S ell (conv.rotationRep (selectorAngle E selectorPrecision)))
    (walkTarget S ell) (walkTarget_unitary S ell) (sourceDeltaRaw S ell) n k
    (2*(6*bitError selectorPrecision)) σ (by have hb := bitError_pos selectorPrecision; positivity) hσ (sourceDeltaRaw_pos S ell) hw hk hn
  rw [sourceDeltaRaw_value, walkTarget, coherentWalkFilter_reindex] at h
  change ‖(nativeUF conv E S ell m precision selectorPrecision n k).matrix -
    (coherentWalkFilter _ (2^m) _).submatrix (paperFilterLayout S ell m) (paperFilterLayout S ell m)‖ ≤ _ at h
  convert h using 1 <;> ring


/-- The preparation's physical layout, with its register size exposed for
native matrix subtraction. -/
def filterLayout (S : EffectiveSourceComputation G) (ell m : ℕ) :
    Basis (m+(1+SourcePreparationPlacement.walkQubits S ell)) ≃
      SourceSimulation.FilterSpace ell (restQubits S) S.catalystQubits (m+4+1) :=
  SourcePreparationPlacement.filterLayout S ell m

def sourcePaperLayout (S : EffectiveSourceComputation G) (ell m : ℕ) :=
  (filterLayout S ell m).trans
    ((SelectedFilter.implementationIndex ell (restQubits S) S.catalystQubits m 4
      SelectedFilter.fourBlockAncillas).trans (SelectedFilter.circuitAuxiliaryIndex (2^m)))

def coordinateIndex (S : EffectiveSourceComputation G) (ell m : ℕ) :=
  (rotationIndex (s := Fin (2^m)) (n := SelectedFilter.BlockDilation HistoryEncoding.BlockAncilla
    (Fin (Fintype.card (Bits ell)) × CanonicalData S))).trans
    ((Equiv.refl (Fin (2^m))).prodCongr ((Equiv.refl (Fin 2)).prodCongr
      (OneCleanQubit.tensorBasis.symm.trans ((Equiv.refl (Fin 2)).prodCongr
        ((Equiv.refl HistoryEncoding.BlockAncilla).prodCongr
          (Fintype.equivFin (Fin (Fintype.card (Bits ell)) × CanonicalData S)).symm)))))


lemma rotationIndex_data {a b : Type*} [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    {s : Type*} [Fintype s] [DecidableEq s] (e : a ≃ b)
    (p : Sum (s × a) (s × a)) :
    rotationIndex ((Equiv.sumCongr ((Equiv.refl s).prodCongr e) ((Equiv.refl s).prodCongr e)) p) =
      ((Equiv.refl s).prodCongr ((Equiv.refl (Fin 2)).prodCongr e)) (rotationIndex p) := by
  rcases p with ⟨j,i⟩ | ⟨j,i⟩ <;> rfl

lemma tensorBasis_data {a b : Type*} (e : a ≃ b) (p : a ⊕ a) :
    OneCleanQubit.tensorBasis.symm ((e.sumCongr e) p) =
      ((Equiv.refl (Fin 2)).prodCongr e) (OneCleanQubit.tensorBasis.symm p) := by
  cases p <;> rfl

lemma rotationIndex_aux {a i : Type*} [Fintype a] [Fintype i] [DecidableEq a] [DecidableEq i]
    (M : ℕ) (p : SelectedFilter.CoherentAux a M × SelectedFilter.DilationIndex i) :
    rotationIndex (SelectedFilter.circuitAuxiliaryIndex M p) =
      (p.1.1.2,(p.1.1.1,SelectedFilter.blockEmbedding p.1.2 p.2)) := by
  rcases p with ⟨⟨⟨b,j⟩,q⟩,i⟩
  fin_cases b <;> rfl

lemma physicalDilation_read (ell s c : ℕ) (q : HistoryEncoding.BlockAncilla)
    (p : Small ell s 0 × SourceSimulation.CatalystData c) :
    OneCleanQubit.tensorBasis.symm (SelectedFilter.blockEmbedding q
      (SelectedFilter.physicalDilationIndex ell s (Fintype.card (Bits c)^2) p)) =
      (p.1.1,(q,(Fintype.equivFin (SelectedFilter.PhysicalHistory ell s (Fintype.card (Bits c)^2)))
        (SelectedFilter.clockIndex ell p.1.2.1,
          ((SourceBias.operatorIndex (WorkSpace s)).symm p.1.2.2.1,p.2)))) := by
  rcases p with ⟨⟨b,clock,work,extra⟩,cat⟩
  fin_cases b <;> rfl

lemma coordinateIndex_source (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (m+(1+SourcePreparationPlacement.walkQubits S ell))) :
    coordinateIndex S ell m (sourcePaperLayout S ell m x) =
      let p := filterLayout S ell m x
      let aux := SelectedFilter.coherentAuxBits m 4 SelectedFilter.fourBlockAncillas p.1.1
      (aux.1.2,(aux.1.1,(p.1.2.1,(aux.2,(SelectedFilter.clockIndex ell p.1.2.2.1,
        ((SourceBias.operatorIndex (WorkSpace (restQubits S))).symm p.1.2.2.2.1,p.2)))))) := by
  simp only [coordinateIndex, sourcePaperLayout, Equiv.trans_apply, rotationIndex_aux,
    SelectedFilter.implementationIndex, Equiv.prodCongr_apply, Equiv.prodAssoc_apply,
    Equiv.refl_apply, physicalDilation_read, Equiv.symm_apply_apply, Prod.map_apply']

lemma coordinateIndex_paper (S : EffectiveSourceComputation G) (ell m : ℕ)
    (x : Basis (m+(1+SourcePreparationPlacement.walkQubits S ell))) :
    coordinateIndex S ell m (paperFilterLayout S ell m x) =
      let pr := registerBasis m (1+SourcePreparationPlacement.walkQubits S ell) x
      let rd := rotationDataIndex (SourcePreparationPlacement.walkQubits S ell) pr.2
      let he := probeTensor (4+(ell+DataQubits S)) (rewireBasis (walkWire S ell) rd.2)
      let ce := SourceHistoryCompilation.layout S ell (rewireBasis (SourceWalkCompilation.prefixWire S ell) he.2)
      (SelectedFilter.bitsBinaryIndex m pr.1,(rd.1,(he.1,((ce.1,ce.2.1),ce.2.2)))) := by
  simp only [coordinateIndex, paperFilterLayout, filterIndex, Equiv.trans_apply, rotationIndex_data,
    Equiv.apply_symm_apply, Equiv.prodCongr_apply, Equiv.refl_apply, walkDataLayout,
    SourceWalkCompilation.walkLayout, probeBasis, tensorBasis_data,
    Equiv.symm_apply_apply, SourceWalkCompilation.encoderLayout,
    SourceHistoryCompilation.enumeratedLayout, HistoryEncoding.encodingIndex, Prod.map_apply', Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk,
    Equiv.symm_apply_apply]

lemma aux_pack (m : ℕ) (phase : Bits m) (rot outer : Fin 2) (block : Bits 3) :
    SelectedFilter.coherentAuxBits m 4 SelectedFilter.fourBlockAncillas
      (SourcePreparationPlacement.packAux m (phase,(rot,(outer,block)))) =
      ((rot,SelectedFilter.bitsBinaryIndex m phase),(outer,uniform3Layout block)) := by
  simp [SelectedFilter.coherentAuxBits, SourcePreparationPlacement.packAux,
    SelectedFilter.fourBlockAncillas, uniform3Layout, tensorBits_register]
  rfl

lemma layout_identity (S : EffectiveSourceComputation G) (ell m : ℕ) :
    paperFilterLayout S ell m = sourcePaperLayout S ell m := by
  apply Equiv.ext
  intro x
  apply (coordinateIndex S ell m).injective
  rw [coordinateIndex_paper, coordinateIndex_source]
  dsimp only
  simp only [filterLayout, SourcePreparationPlacement.filterLayout,
    SourcePreparationPlacement.filterRegroup, SourcePreparationPlacement.unusedIndex,
    SourcePreparationPlacement.unusedRegroup, SourcePreparationPlacement.unusedReadIndex,
    Equiv.trans_apply, Equiv.prodCongr_apply, Prod.map_apply', Equiv.refl_apply, aux_pack,
    Equiv.coe_fn_mk]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
  all_goals dsimp only
  · apply congrArg (SelectedFilter.bitsBinaryIndex m)
    funext i
    refine Eq.trans ?_ (SourcePreparationPlacement.logicalLayout_unused S ell m x (Sum.inl i)).symm
    rfl
  · refine Eq.trans ?_ (SourcePreparationPlacement.logicalLayout_unused S ell m x (Sum.inr (Sum.inl 0))).symm
    rfl
  · have h := SourcePreparationPlacement.logicalLayout_selected S ell m x (Sum.inl 0)
    change (SourcePreparationPlacement.logicalLayout S ell m x).1.1 = _ at h
    exact (show _ = x (SourcePreparationPlacement.allPositions S ell m (Sum.inl (Sum.inl 0))) from rfl).trans h.symm
  · apply Prod.ext
    all_goals dsimp only
    · refine Eq.trans ?_ (SourcePreparationPlacement.logicalLayout_unused S ell m x
        (Sum.inr (Sum.inr (Sum.inl (Sum.inl 0))))).symm
      rfl
    · dsimp only [SourceHistoryCompilation.layout,historyALayout,historyLayout,differenceLayout,
        Equiv.prodCongr_apply,Prod.map_apply',Equiv.trans_apply,Equiv.refl_apply]
      apply congrArg uniform3Layout
      funext i
      refine Eq.trans ?_ (SourcePreparationPlacement.logicalLayout_unused S ell m x
        (Sum.inr (Sum.inr (Sum.inl (Sum.inr i))))).symm
      rfl
  · apply Prod.ext
    all_goals dsimp only
    · apply congrArg (SelectedFilter.clockIndex ell)
      funext i
      have h := SourcePreparationPlacement.logicalLayout_selected S ell m x (Sum.inr (Sum.inl i))
      change (SourcePreparationPlacement.logicalLayout S ell m x).1.2.1 i = _ at h
      exact (show _ = x (SourcePreparationPlacement.allPositions S ell m (Sum.inl (Sum.inr (Sum.inl i)))) from rfl).trans h.symm

    · refine Eq.trans ?_ (SourceDataReadback.dataTail_readback S ell m x)
      apply congrArg (nativeDataIndex S)
      funext i
      apply congrArg x
      apply Fin.ext
      dsimp [SourceDataReadback.dataTail, SourceHistoryCompilation.layout, historyALayout,
        historyLayout, differenceLayout, rewireBasis, walkWire, SourceWalkCompilation.prefixWire,
        rotationDataIndex, tensorBits, registerBasis, probeTensor]
      omega

/-- The already-proved source filter, now on the very same actual physical
wires used by native F preparation. -/
def sourceUF (S : EffectiveSourceComputation G) (ell m : ℕ) :=
  SelectedFilter.physicalCoherentFilter ell (restQubits S) S.catalystQubits m 4
    SelectedFilter.fourBlockAncillas (SourceWalkCompilation.idealEncoder S ell)
    (0,zeroSelector3)
    (biasLam (Fintype.card (Bits ell)) (Fintype.card (WorkSpace (restQubits S))))

lemma sourceUF_layout (S : EffectiveSourceComputation G) (ell m : ℕ) :
    (sourceUF S ell m).submatrix (filterLayout S ell m) (filterLayout S ell m) =
      (coherentWalkFilter (SelectedFilter.blockWalk (SourceWalkCompilation.idealEncoder S ell)
        (0,zeroSelector3)) (2^m)
        (biasDelta (Fintype.card (Bits ell)) (Fintype.card (WorkSpace (restQubits S))))).submatrix
          (sourcePaperLayout S ell m) (sourcePaperLayout S ell m) := rfl

theorem nativeUF_error_physical (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : FourierCompilation.StandardQFTCorrectness)
    (S : EffectiveSourceComputation G) (ell m precision selectorPrecision n k : ℕ)
    (σ : ℝ) (hσ : 0 ≤ σ) (hk : bitError k ≤ σ/4)
    (hn : bitError n ≤ ((sourceDeltaRaw S ell).value:ℝ)*σ/40) :
    ‖(nativeUF conv E S ell m precision selectorPrecision n k).matrix -
      (sourceUF S ell m).submatrix (filterLayout S ell m) (filterLayout S ell m)‖ ≤
      24*(2^m:ℕ)*bitError selectorPrecision +
        16*(m*(m+2):ℕ)*bitError precision + σ := by
  rw [sourceUF_layout, ←layout_identity]
  exact nativeUF_error_paper conv E standard S ell m precision selectorPrecision n k σ hσ hk hn

/-- Final source-level operator-norm bridge: the returned actual native list
approximates the existing implementation record. Spectral data appear only
in that record's correctness proof, and are never circuit-generation data. -/
theorem nativeUF_error_implementation (conv : GateConvention G) (E : ElementaryAnalyticInputs)
    (standard : FourierCompilation.StandardQFTCorrectness)
    (S : EffectiveSourceComputation G) (D : SourceCircuitSimulation.SpectralInput S)
    (precision selectorPrecision n k : ℕ) (σ : ℝ) (hσ : 0 ≤ σ)
    (hk : bitError k ≤ σ/4)
    (hn : bitError n ≤ ((sourceDeltaRaw S (SourceCircuitSimulation.clockBits S)).value:ℝ)*σ/40) :
    let ell := SourceCircuitSimulation.clockBits S
    let m := SelectedFilter.sourcePhaseBits ell (restQubits S)
    ‖(nativeUF conv E S ell m precision selectorPrecision n k).matrix -
      (SourceCircuitSimulation.implementation S D).matrix.submatrix
        (filterLayout S ell m) (filterLayout S ell m)‖ ≤
      24*(2^m:ℕ)*bitError selectorPrecision +
        16*(m*(m+2):ℕ)*bitError precision + σ := by
  exact nativeUF_error_physical conv E standard S (SourceCircuitSimulation.clockBits S)
    (SelectedFilter.sourcePhaseBits (SourceCircuitSimulation.clockBits S) (restQubits S))
    precision selectorPrecision n k σ hσ hk hn

end Paper25.FullFilterPlacement
