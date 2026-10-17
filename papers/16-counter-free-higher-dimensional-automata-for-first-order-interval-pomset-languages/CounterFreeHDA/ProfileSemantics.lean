import CounterFreeHDA.DeletionCorners

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem prefixResidual_comp {U V : UCube} (P : Prefix U) (B : BoundedArrow U V) :
    prefixResidual (P.comp B) = rightAction (prefixResidual P) B := by
  ext Q
  exact Actual.originalHDA.language_iso (BoundedArrow.assocIso P B Q)

theorem prefixResidual_iso {U : UCube} (P Q : Prefix U) (φ : PomsetIso P.pom.val Q.pom.val) :
    prefixResidual P = prefixResidual Q := by
  ext R
  exact Actual.originalHDA.language_iso (BoundedArrow.compIso φ (PomsetIso.refl R.pom.val))

theorem rightAction_iso {U V : UCube} (R : Set (Tail U)) (A B : BoundedArrow U V)
    (φ : PomsetIso A.pom.val B.pom.val)
    (hR : ∀ Q Q' : Tail U, PomsetIso Q.pom.val Q'.pom.val → (Q ∈ R ↔ Q' ∈ R)) :
    rightAction R A = rightAction R B := by
  ext Q
  exact hR _ _ (BoundedArrow.compIso φ (PomsetIso.refl Q.pom.val))

theorem suffix_iso {U : UCube} (x : Subset (size U.1)) (Q Q' : Tail U) (φ : PomsetIso Q.pom.val Q'.pom.val) :
    Q ∈ suffix x ↔ Q' ∈ suffix x := by
  exact exists_congr (fun i => and_congr Iff.rfl
    (congrArg (fun s => Actual.indexCell Completion.emptyCube 0 ∈ s)
      (Actual.originalHDA.toPrecubical.dPom_iso φ (Actual.indexCell U i))).to_iff)

theorem residual_wordAction {U V : UCube} (p : Word U V) (r : Kind U) :
    rightAction (residualLanguage U r) (BoundedArrow.ofWord p) = residualLanguage V (wordKind p r) := by
  have hx : rightAction (suffix (representative U.1 r)) (BoundedArrow.ofWord p) =
      suffix (originalExecute p (representative U.1 r)) := by
    ext Q
    constructor
    · rintro ⟨i,hi,hr⟩
      obtain ⟨z,hz,hQ⟩ := (Actual.originalHDA.toPrecubical.dPom_comp (BoundedArrow.ofWord p) Q _ _).mp hr
      obtain ⟨j,rfl⟩ := Actual.indexCell_surjective V z
      exact ⟨j,(originalExecute_iff p _ j).mpr
        ⟨i,hi,(Actual.originalHDA.toPrecubical.dPom_word p _ _).mp hz⟩,hQ⟩
    · rintro ⟨j,hj,hQ⟩
      obtain ⟨i,hi,hp⟩ := (originalExecute_iff p _ j).mp hj
      exact ⟨i,hi,(Actual.originalHDA.toPrecubical.dPom_comp (BoundedArrow.ofWord p) Q _ _).mpr
        ⟨Actual.indexCell V j,(Actual.originalHDA.toPrecubical.dPom_word p _ _).mpr hp,hQ⟩⟩
  exact hx.trans (represented_suffix_eq (execute_represents p _ r (representative_represents U r))
    (representative_represents V _))

theorem residual_arrowAction {U V : UCube} (B : BoundedArrow U V) (r : Kind U) :
    rightAction (residualLanguage U r) B = residualLanguage V (wordKind B.representative r) := by
  exact (rightAction_iso (residualLanguage U r) B (BoundedArrow.ofWord B.representative) B.representativeIso.symm
    (suffix_iso (representative U.1 r))).trans (residual_wordAction B.representative r)

/-- Exact deletion-profile update: deletion is performed on real target
events; the update is the right action of the genuinely reduced factor. -/
theorem profile_comp_coordinate {U V : UCube} (P : Prefix U) (B : BoundedArrow U V) (D : Finset (Fin V.dim)) :
    profile (P.comp B) D = wordKind (deletedArrow B D).representative
      (profile P (B.toArrow.pullTargetDeletion D)) := by
  apply residualLanguage_injective
  rw [profile_semantics]
  have he := prefixResidual_iso _ _ (deletedPrefix_compIso P B D)
  exact he.symm.trans ((prefixResidual_comp _ _).trans
    (by rw [← profile_semantics]; exact residual_arrowAction _ _))

end CounterFreeHDA.Appendix.Residual
