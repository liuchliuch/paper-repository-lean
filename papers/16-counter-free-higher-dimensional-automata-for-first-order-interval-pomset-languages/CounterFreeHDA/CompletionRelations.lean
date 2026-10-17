import CounterFreeHDA.CompletionCounter
import CounterFreeHDA.EffectiveDiagrams

namespace CounterFreeHDA.Appendix.Completion
open Cubical

def startRel {U V : UCube} (f : Cubical.Face U V) : BRel (profileSize U.1) (profileSize V.1) :=
  fun i j => decide (completionHDA.face f (indexCell V j) = indexCell U i)

def stopRel {U V : UCube} (f : Cubical.Face U V) : BRel (profileSize V.1) (profileSize U.1) :=
  fun i j => decide (completionHDA.face f (indexCell V i) = indexCell U j)

def stepRel : {U V : UCube} → Step U V → BRel (profileSize U.1) (profileSize V.1)
  | _,_,.start f _ _ => startRel f
  | _,_,.stop f _ _ => stopRel f

def wordRel : {U V : UCube} → Word U V → BRel (profileSize U.1) (profileSize V.1)
  | _,_,.nil U => ident (profileSize U.1)
  | _,_,.cons s p => comp (stepRel s) (wordRel p)

/-- The table calculation describes the entire actual nondeterministic
endpoint relation of the fixed elementary ST word. -/
theorem wordRel_iff {U V : UCube} (p : Word U V) (i : Fin (profileSize U.1)) (j : Fin (profileSize V.1)) :
    wordRel p i j = true ↔ completionHDA.Run p (indexCell U i) (indexCell V j) := by
  induction p with
  | nil U =>
    simp only [wordRel,ident,decide_eq_true_eq,completionHDA.toPrecubical.run_nil_iff]
    exact ⟨fun h => congrArg (indexCell U) h,fun h => indexCell_injective U h⟩
  | cons s p ih =>
    cases s with
    | start f hl hd =>
      rw [completionHDA.toPrecubical.run_start_iff]
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
      rw [completionHDA.toPrecubical.run_stop_iff]
      rw [wordRel,comp,decide_eq_true_eq]
      change (∃ l, stopRel f i l = true ∧ wordRel p l j = true) ↔ _
      simp only [stopRel,decide_eq_true_eq]
      constructor
      · rintro ⟨l,hl',hp⟩
        exact hl'.symm ▸ (ih l j).mp hp
      · intro hp
        obtain ⟨l,hl'⟩ := indexCell_surjective _ (completionHDA.face f (indexCell _ i))
        exact ⟨l,hl'.symm,(ih l j).mpr (hl' ▸ hp)⟩


end CounterFreeHDA.Appendix.Completion
