import CounterFreeHDA.AppendixLanguageInvariant

namespace CounterFreeHDA.Appendix.Compare
open Cubical

theorem action_ident (x : Subset n) : action (ident n) x = x := by
  funext j
  simp only [action,ident,decide_eq_true_eq]
  simp

theorem action_comp (r : BRel n m) (s : BRel m l) (x : Subset n) :
    action s (action r x) = action (comp r s) x := by
  funext j
  unfold action comp
  apply decide_eq_decide.mpr
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨a,⟨b,hx,hr⟩,hs⟩
    exact ⟨b,hx,a,hr,hs⟩
  · rintro ⟨a,hx,b,hr,hs⟩
    exact ⟨b,⟨a,hx,hr⟩,hs⟩

theorem originalExecute_rel {U V : UCube} (p : Word U V) (x : Subset (size U.1)) :
    originalExecute p x = action (Actual.wordRel p) x := by
  induction p with
  | nil U => exact (action_ident x).symm
  | cons s p ih =>
    change originalExecute p (action (Actual.stepRel s) x) = action (comp (Actual.stepRel s) (Actual.wordRel p)) x
    rw [ih,action_comp]

theorem completedExecute_rel {U V : UCube} (p : Word U V) (x : Subset (Completion.profileSize U.1)) :
    completedExecute p x = action (Completion.wordRel p) x := by
  induction p with
  | nil U => exact (action_ident x).symm
  | cons s p ih =>
    change completedExecute p (action (Completion.stepRel s) x) = action (comp (Completion.stepRel s) (Completion.wordRel p)) x
    rw [ih,action_comp]

theorem originalExecute_iff {U V : UCube} (p : Word U V) (x : Subset (size U.1)) (j : Fin (size V.1)) :
    originalExecute p x j = true ↔ ∃ i, x i = true ∧ Actual.originalHDA.Run p (Actual.indexCell U i) (Actual.indexCell V j) := by
  rw [originalExecute_rel]
  simp only [action,decide_eq_true_eq,Actual.wordRel_iff]

theorem completedExecute_iff {U V : UCube} (p : Word U V) (x : Subset (Completion.profileSize U.1)) (j : Fin (Completion.profileSize V.1)) :
    completedExecute p x j = true ↔ ∃ i, x i = true ∧ Completion.completionHDA.Run p (Completion.indexCell U i) (Completion.indexCell V j) := by
  rw [completedExecute_rel]
  simp only [action,decide_eq_true_eq,Completion.wordRel_iff]

theorem originalExecute_initial {V : UCube} (p : Word Completion.emptyCube V) (j : Fin (size V.1)) :
    originalExecute p (mask 2 1) j = true ↔
      Actual.originalHDA.Run p (Actual.indexCell Completion.emptyCube 0) (Actual.indexCell V j) := by
  rw [originalExecute_iff]
  have hm : ∀ i : Fin 2, mask 2 1 i = true ↔ i = 0 := by decide
  simp only [hm,exists_eq_left,true_and]

theorem completedExecute_initial {V : UCube} (p : Word Completion.emptyCube V) (j : Fin (Completion.profileSize V.1)) :
    completedExecute p (mask 3 1) j = true ↔
      Completion.completionHDA.Run p (Completion.indexCell Completion.emptyCube 0) (Completion.indexCell V j) := by
  rw [completedExecute_iff]
  have hm : ∀ i : Fin 3, mask 3 1 i = true ↔ i = 0 := by decide
  simp only [hm,exists_eq_left,true_and]

/-- Equality of acceptance for every actual closed ST word, proved by the
kernel-checked finite subset invariant, without assuming language equality. -/
theorem closed_word_acceptance (p : Word Completion.emptyCube Completion.emptyCube) :
    originalExecute p (mask 2 1) 0 = true ↔
      completedExecute p (mask 3 1) 0 = true ∨ completedExecute p (mask 3 1) 2 = true :=
  accepting_invariant _ _ (execute_invariant p _ _ initial_invariant)

theorem cube_eq_empty {U : UCube} (h : U.dim = 0) : U = Completion.emptyCube := by
  apply Cube.interface_injective
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  exact ⟨h,funext fun i => Subsingleton.elim _ _⟩

end CounterFreeHDA.Appendix.Compare
