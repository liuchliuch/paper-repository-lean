import Paper25.PreparationCompilation
import Paper25.ClockUniformCompilation

/-! Exact chronological rows of the already constructed elementary F list. -/
noncomputable section
namespace Paper25.OperationalModel.UniformCompilation
open LocalCompilation
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2400000
variable {G : EffectiveGateSet}

lemma compileElementary_liftLeft (conv : GateConvention G) {q : ℕ}
    (g : LocalGate StatePreparationLocal.elementary q) (r : ℕ) :
    compileElementaryGate conv (StatePreparationLocal.liftLeft g r) =
      (compileElementaryGate conv g).map (fun a => LocalCompilation.liftLeft a r) := by
  unfold compileElementaryGate embedCircuit
  simp only [List.map_map,Function.comp_def]
  congr 1

lemma compileElementary_liftRight (conv : GateConvention G) {r : ℕ}
    (g : LocalGate StatePreparationLocal.elementary r) (q : ℕ) :
    compileElementaryGate conv (StatePreparationLocal.liftRight g q) =
      (compileElementaryGate conv g).map (fun a => LocalCompilation.liftRight a q) := by
  unfold compileElementaryGate embedCircuit
  simp only [List.map_map,Function.comp_def]
  congr 1

lemma compileElementary_tensor (conv : GateConvention G) {q r : ℕ}
    (C : Circuit StatePreparationLocal.elementary q)
    (D : Circuit StatePreparationLocal.elementary r) :
    compileElementary conv (StatePreparationLocal.tensorCircuit C D) =
      LocalCompilation.tensorCircuit (compileElementary conv C) (compileElementary conv D) := by
  simp only [StatePreparationLocal.tensorCircuit, compileElementary,List.flatMap_append,
    List.flatMap_map,LocalCompilation.tensorCircuit,List.map_flatMap,Function.comp_def,
    compileElementary_liftLeft,compileElementary_liftRight]

/-- A contiguous physical row embedding. -/
def intervalWires (q k offset : ℕ) (h : offset+k≤q) : Fin k ↪ Fin q where
  toFun i := ⟨offset+i.val,by have := i.isLt; omega⟩
  inj' i j h := by apply Fin.ext; have := congrArg Fin.val h; dsimp at this; omega

def bellRow (conv : GateConvention G) (s : ℕ) (j : Fin s) :
    EffectiveCircuit G (StatePreparationLocal.bellSize s) :=
  embedCircuit (placementOfEmbedding
    (intervalWires (StatePreparationLocal.bellSize s) 2 (2*j.val)
      (by have := j.isLt; rw [StatePreparationLocal.bellSize_eq]; omega)))
    (compileElementary conv StatePreparationLocal.bellLocalPair)

lemma bellRow_zero (conv : GateConvention G) (s : ℕ) :
    bellRow conv (s+1) 0 =
      (compileElementary conv StatePreparationLocal.bellLocalPair).map
        (fun g => LocalCompilation.liftLeft g (StatePreparationLocal.bellSize s)) := by
  unfold bellRow embedCircuit
  congr 1
  funext g
  unfold embedGate LocalCompilation.liftLeft
  congr 1
  apply congrArg placementOfEmbedding
  ext i
  change 0+(active g.placement i).val=(active g.placement i).val
  omega

lemma bellRow_succ (conv : GateConvention G) (s : ℕ) (j : Fin s) :
    bellRow conv (s+1) j.succ =
      (bellRow conv s j).map (fun g => LocalCompilation.liftRight g 2) := by
  unfold bellRow embedCircuit
  simp only [List.map_map,Function.comp_def]
  congr 1
  funext g
  unfold embedGate LocalCompilation.liftRight
  congr 1
  apply congrArg placementOfEmbedding
  ext i
  change 2*(j.val+1)+(active g.placement i).val = 2+(2*j.val+(active g.placement i).val)
  omega

lemma bell_eq_rows (conv : GateConvention G) (s : ℕ) :
    compileElementary conv (StatePreparationLocal.bellLocal s) =
      (List.ofFn (bellRow conv s)).flatten := by
  induction s with
  | zero => simp [StatePreparationLocal.bellLocal,compileElementary]
  | succ s ih =>
    rw [StatePreparationLocal.bellLocal,compileElementary_tensor,ih,
      LocalCompilation.tensorCircuit,List.ofFn_succ,List.flatten_cons,bellRow_zero]
    simp only [bellRow_succ,List.map_flatten,List.map_ofFn,Function.comp_def]

def preparationClockRow (conv : GateConvention G) (ell : ℕ) (t : StatePreparation.Bits ell) (j : Fin ell) :
    EffectiveCircuit G (StatePreparationLocal.clockSize ell) :=
  if t j=0 then [] else
    embedCircuit (placementOfEmbedding
      (intervalWires (StatePreparationLocal.clockSize ell) 1 j.val
        (by have := j.isLt; rw [StatePreparationLocal.clockSize_eq]; omega)))
      (compileElementary conv StatePreparationLocal.xCircuit)

lemma preparationClockRow_zero (conv : GateConvention G) (ell : ℕ) (t : StatePreparation.Bits (ell+1)) :
    preparationClockRow conv (ell+1) t 0 =
      (compileElementary conv (if t 0=0 then ([] : Circuit StatePreparationLocal.elementary 1)
        else StatePreparationLocal.xCircuit)).map
          (fun g => LocalCompilation.liftLeft g (StatePreparationLocal.clockSize ell)) := by
  unfold preparationClockRow
  split_ifs with h
  · rfl
  · unfold embedCircuit
    congr 1
    funext g
    unfold embedGate LocalCompilation.liftLeft
    congr 1
    apply congrArg placementOfEmbedding
    ext i
    change 0+(active g.placement i).val=(active g.placement i).val
    omega

lemma preparationClockRow_succ (conv : GateConvention G) (ell : ℕ) (t : StatePreparation.Bits (ell+1))
    (j : Fin ell) :
    preparationClockRow conv (ell+1) t j.succ =
      (preparationClockRow conv ell (fun i => t i.succ) j).map (fun g => LocalCompilation.liftRight g 1) := by
  unfold preparationClockRow
  split_ifs with h
  · rfl
  · unfold embedCircuit
    simp only [List.map_map,Function.comp_def]
    congr 1
    funext g
    unfold embedGate LocalCompilation.liftRight
    congr 1
    apply congrArg placementOfEmbedding
    ext i
    change j.val+1+(active g.placement i).val=1+(j.val+(active g.placement i).val)
    omega

lemma clock_eq_rows (conv : GateConvention G) (ell : ℕ) (t : StatePreparation.Bits ell) :
    compileElementary conv (StatePreparationLocal.clockLocal ell t) =
      (List.ofFn (preparationClockRow conv ell t)).flatten := by
  induction ell with
  | zero => simp [StatePreparationLocal.clockLocal,compileElementary]
  | succ ell ih =>
    rw [StatePreparationLocal.clockLocal,compileElementary_tensor,ih,
      LocalCompilation.tensorCircuit,List.ofFn_succ,List.flatten_cons,preparationClockRow_zero]
    simp only [preparationClockRow_succ,List.map_flatten,List.map_ofFn,Function.comp_def]

end Paper25.OperationalModel.UniformCompilation
