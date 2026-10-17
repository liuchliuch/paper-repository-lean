import CounterFreeHDA.AppendixCells
import CounterFreeHDA.CoproductCounterFree
import CounterFreeHDA.EffectiveDiagrams

namespace CounterFreeHDA.Appendix

theorem comp_ident (r : BRel n m) : comp r (ident m) = r := by
  funext i j
  simp only [comp,ident,decide_eq_true_eq]
  simp

theorem ident_comp (r : BRel n m) : comp (ident n) r = r := by
  funext i j
  simp only [comp,ident,decide_eq_true_eq]
  simp

theorem comp_assoc (r : BRel n m) (s : BRel m l) (t : BRel l q) :
    comp (comp r s) t = comp r (comp s t) := by
  funext i j
  unfold comp
  apply decide_eq_decide.mpr
  simp only [comp,decide_eq_true_eq]
  constructor
  · rintro ⟨a,⟨b,hr,hs⟩,ht⟩
    exact ⟨b,hr,a,hs,ht⟩
  · rintro ⟨a,hr,b,hs,ht⟩
    exact ⟨b,⟨a,hr,hs⟩,ht⟩

end CounterFreeHDA.Appendix

namespace CounterFreeHDA.Appendix.Actual
open Cubical
attribute [local instance] Effective.faceFintype Effective.faceDecidableEq Effective.lowerDecidable Effective.upperDecidable
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def indexCell (U : UCube) (i : Fin (size U.1)) : originalHDA.Cell U := ⟨model U i,⟨i,rfl⟩⟩

theorem indexCell_injective (U : UCube) : Function.Injective (indexCell U) :=
  fun _ _ h => model_injective U (congrArg Subtype.val h)

theorem indexCell_surjective (U : UCube) : Function.Surjective (indexCell U) := by
  rintro ⟨x,i,rfl⟩
  exact ⟨i,rfl⟩

def startRel {U V : UCube} (f : Cubical.Face U V) : BRel (size U.1) (size V.1) :=
  fun i j => decide (originalHDA.face f (indexCell V j) = indexCell U i)

def stopRel {U V : UCube} (f : Cubical.Face U V) : BRel (size V.1) (size U.1) :=
  fun i j => decide (originalHDA.face f (indexCell V i) = indexCell U j)

def stepRel : {U V : UCube} → Step U V → BRel (size U.1) (size V.1)
  | _,_,.start f _ _ => startRel f
  | _,_,.stop f _ _ => stopRel f

/-- Check the actual face table against the complete typed relation tables,
for either event position, directly in the Lean kernel. -/
theorem start_table : ∀ (U V : UCube) (f : Cubical.Face U V), f.Lower → V.dim = U.dim+1 →
    ∀ a : Fin 3, ∀ r ∈ table a U.1, comp r (startRel f) ∈ table a V.1 := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V), f.Lower → V.dim = U.dim+1 →
      ∀ a : Fin 3, ∀ r ∈ table a U.1, comp r (startRel f) ∈ table a V.1) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem stop_table : ∀ (U V : UCube) (f : Cubical.Face U V), f.Upper → V.dim = U.dim+1 →
    ∀ a : Fin 3, ∀ r ∈ table a V.1, comp r (stopRel f) ∈ table a U.1 := by
  let dec : Decidable (∀ (U V : UCube) (f : Cubical.Face U V), f.Upper → V.dim = U.dim+1 →
      ∀ a : Fin 3, ∀ r ∈ table a V.1, comp r (stopRel f) ∈ table a U.1) := by
    refine @Fintype.decidableForallFintype _ _ (fun U => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun V => ?_) inferInstance
    refine @Fintype.decidableForallFintype _ _ (fun f => ?_) (Effective.faceFintype U V)
    infer_instance
  exact of_decide_eq_true (by rfl : @decide _ dec = true)

theorem step_table {U V : UCube} (s : Step U V) {a : Fin 3}
    (r : BRel (size a) (size U.1)) (hr : r ∈ table a U.1) : comp r (stepRel s) ∈ table a V.1 := by
  cases s with
  | start f hl hd => exact start_table _ _ f hl hd a r hr
  | stop f hu hd => exact stop_table _ _ f hu hd a r hr

def wordRel : {U V : UCube} → Word U V → BRel (size U.1) (size V.1)
  | _,_,.nil U => ident (size U.1)
  | _,_,.cons s p => comp (stepRel s) (wordRel p)

theorem word_table_extend {U V : UCube} (p : Word U V) {a : Fin 3}
    (r : BRel (size a) (size U.1)) (hr : r ∈ table a U.1) : comp r (wordRel p) ∈ table a V.1 := by
  induction p with
  | nil U => simpa only [wordRel,comp_ident] using hr
  | cons s p ih =>
    rw [wordRel,← comp_assoc]
    exact ih _ (step_table s r hr)

theorem word_table {U V : UCube} (p : Word U V) : wordRel p ∈ table U.1 V.1 := by
  simpa only [ident_comp] using word_table_extend p (ident (size U.1)) (table_ident U.1)

/-- The table calculation describes the entire actual nondeterministic
endpoint relation of the fixed elementary ST word. -/
theorem wordRel_iff {U V : UCube} (p : Word U V) (i : Fin (size U.1)) (j : Fin (size V.1)) :
    wordRel p i j = true ↔ originalHDA.Run p (indexCell U i) (indexCell V j) := by
  induction p with
  | nil U =>
    simp only [wordRel,ident,decide_eq_true_eq,originalHDA.toPrecubical.run_nil_iff]
    exact ⟨fun h => congrArg (indexCell U) h,fun h => indexCell_injective U h⟩
  | cons s p ih =>
    cases s with
    | start f hl hd =>
      rw [originalHDA.toPrecubical.run_start_iff]
      rw [wordRel,comp,decide_eq_true_eq]
      change (∃ l, startRel f i l = true ∧ wordRel p l j = true) ↔ _
      simp only [startRel,decide_eq_true_eq]
      constructor
      · rintro ⟨l,hl',hp⟩
        exact ⟨indexCell _ l,hl'.symm,(ih l j).mp hp⟩
      · rintro ⟨z,hz,hp⟩
        obtain ⟨l,rfl⟩ := indexCell_surjective _ z
        exact ⟨l,hz.symm,(ih l j).mpr hp⟩
    | stop f hu hd =>
      rw [originalHDA.toPrecubical.run_stop_iff]
      rw [wordRel,comp,decide_eq_true_eq]
      change (∃ l, stopRel f i l = true ∧ wordRel p l j = true) ↔ _
      simp only [stopRel,decide_eq_true_eq]
      constructor
      · rintro ⟨l,hl',hp⟩
        exact hl'.symm ▸ (ih l j).mp hp
      · intro hp
        obtain ⟨l,hl'⟩ := indexCell_surjective _ (originalHDA.face f (indexCell _ i))
        exact ⟨l,hl'.symm,(ih l j).mpr (hl' ▸ hp)⟩

end CounterFreeHDA.Appendix.Actual
