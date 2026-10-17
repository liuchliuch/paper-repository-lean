import CounterFreeHDA.ResidualClassification

namespace CounterFreeHDA.Appendix.Actual
open Cubical

theorem stepPomset_relation {U V : UCube} (s : Step U V) (i : Fin (size U.1)) (j : Fin (size V.1)) :
    indexCell V j ∈ originalHDA.toPrecubical.dPom (indexCell U i) s.label.pom ↔ stepRel s i j = true := by
  let A := BoundedArrow.ofStep s
  have φ := A.identityRightIso
  change indexCell V j ∈ originalHDA.toPrecubical.dPom (indexCell U i) A.pom ↔ _
  rw [← originalHDA.toPrecubical.dPom_iso φ (indexCell U i)]
  change indexCell V j ∈ originalHDA.toPrecubical.dPom (indexCell U i) (Word.cons s (.nil V)).label.pom ↔ _
  rw [originalHDA.toPrecubical.dPom_word]
  cases s with
  | start f hl hd =>
    rw [originalHDA.toPrecubical.run_start_iff]
    simp only [originalHDA.toPrecubical.run_nil_iff,exists_eq_right,stepRel,startRel,decide_eq_true_eq]
    exact eq_comm
  | stop f hu hd =>
    rw [originalHDA.toPrecubical.run_stop_iff,originalHDA.toPrecubical.run_nil_iff]
    simp only [stepRel,stopRel,decide_eq_true_eq]

end CounterFreeHDA.Appendix.Actual

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

def rightAction {U V : UCube} (R : Set (Tail U)) (E : BoundedArrow U V) : Set (Tail V) :=
  {Q | E.comp Q ∈ R}

theorem suffix_step {U V : UCube} (x : Subset (size U.1)) (s : Step U V) :
    rightAction (suffix x) (BoundedArrow.ofStep s) = suffix (action (Actual.stepRel s) x) := by
  ext Q
  change (∃ i, x i = true ∧ Actual.indexCell Completion.emptyCube 0 ∈
    Actual.originalHDA.toPrecubical.dPom (Actual.indexCell U i) ((BoundedArrow.ofStep s).comp Q).pom) ↔ _
  constructor
  · rintro ⟨i,hi,hr⟩
    obtain ⟨z,hz,hQ⟩ := (Actual.originalHDA.toPrecubical.dPom_comp (BoundedArrow.ofStep s) Q _ _).mp hr
    obtain ⟨j,rfl⟩ := Actual.indexCell_surjective V z
    exact ⟨j,decide_eq_true_eq.mpr ⟨i,hi,(Actual.stepPomset_relation s i j).mp hz⟩,hQ⟩
  · rintro ⟨j,hj,hQ⟩
    obtain ⟨i,hi,hs⟩ := decide_eq_true_eq.mp hj
    exact ⟨i,hi,(Actual.originalHDA.toPrecubical.dPom_comp (BoundedArrow.ofStep s) Q _ _).mpr
      ⟨Actual.indexCell V j,(Actual.stepPomset_relation s i j).mpr hs,hQ⟩⟩

/-- The complete elementary table in A.2 is the right action on actual
canonical suffix languages, rather than an assumed action on finite names. -/
theorem elementary_residual_action {U V : UCube} (s : Step U V) (r : Kind U) :
    rightAction (residualLanguage U r) (BoundedArrow.ofStep s) = residualLanguage V (stepKind s r) := by
  change rightAction (suffix (representative U.1 r)) (BoundedArrow.ofStep s) = _
  rw [suffix_step]
  apply represented_suffix_eq ?_ (representative_represents V _)
  cases s with
  | start f hl hd => exact represents_start _ _ f hl hd _ _ (representative_represents U r)
  | stop f hu hd => exact represents_stop _ _ f hu hd _ _ (representative_represents U r)

end CounterFreeHDA.Appendix.Residual
