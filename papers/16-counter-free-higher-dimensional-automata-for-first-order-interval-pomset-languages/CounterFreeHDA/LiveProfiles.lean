import CounterFreeHDA.ProfileInvariance
import CounterFreeHDA.UnarySteps

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem profileCode_ofWord {U : UCube} (p : Word Completion.emptyCube U) :
    profileCode (BoundedArrow.ofWord p) = executeCode p (fun _ => 0) := by
  have he := profileCode_append (BoundedArrow.ident Completion.emptyCube) p
  have hi := profileCode_iso _ _ (BoundedArrow.ofWord p).identityLeftIso
  exact hi.symm.trans (by simpa only [initial_profileCode] using he)

/-- All actual live deletion profiles, over all actual prefix pomsets,
are exactly among the ten displayed tuples. Dead profiles are unrestricted. -/
theorem live_profile_exhaustive {U : UCube} (P : Prefix U) (hl : liveCode U (profileCode P)) :
    ∃ i : Fin (Completion.profileSize U.1), profileCode P = templateCode U i := by
  have he : profileCode P = executeCode P.representative (fun _ => 0) :=
    (profileCode_iso _ _ P.representativeIso).symm.trans (profileCode_ofWord P.representative)
  have hinit : (fun _ => (0 : Fin 4)) = templateCode Completion.emptyCube 0 := by rfl
  rcases execute_templates P.representative (fun _ => 0) (Or.inr ⟨0,hinit⟩) with hd | ht
  · exact False.elim (hd (he ▸ hl))
  · exact ht.imp (fun i hi => he.trans hi)

theorem live_profile_witnesses (U : UCube) (i : Fin (Completion.profileSize U.1)) :
    ∃ p : Word Completion.emptyCube U, executeCode p (fun _ => 0) = templateCode U i := by
  rcases U with ⟨n,lab⟩
  fin_cases n
  · have hl : lab = (Fin.elim0 : Fin 0 → Unit) := Subsingleton.elim _ _
    subst lab
    change Fin 3 at i
    fin_cases i
    · exact ⟨.nil _,by decide⟩
    · exact ⟨Unary.a,by decide⟩
    · exact ⟨Unary.a.append Unary.a,by decide⟩
  · have hl : lab = (fun _ : Fin 1 => ()) := Subsingleton.elim _ _
    subst lab
    change Fin 4 at i
    fin_cases i
    · exact ⟨Unary.E,by decide⟩
    · exact ⟨Unary.F,by decide⟩
    · exact ⟨Unary.G,by decide⟩
    · exact ⟨(Unary.a.append Unary.a).append Unary.E,by decide⟩
  · have hl : lab = (fun _ : Fin 2 => ()) := Subsingleton.elim _ _
    subst lab
    change Fin 3 at i
    fin_cases i
    · exact ⟨Unary.H,by decide⟩
    · exact ⟨Unary.I,by decide⟩
    · exact ⟨((Unary.a.append Unary.a).append Unary.E).append (.cons Unary.s1 (.nil Unary.two)),by decide⟩

theorem live_profile_reachable (U : UCube) (i : Fin (Completion.profileSize U.1)) :
    ∃ P : Prefix U, profileCode P = templateCode U i := by
  obtain ⟨p,hp⟩ := live_profile_witnesses U i
  exact ⟨BoundedArrow.ofWord p,(profileCode_ofWord p).trans hp⟩

/-- Equality of profile coordinates is actual residual-language equality. -/
theorem profileCode_semantically_injective {U : UCube} (P Q : Prefix U) :
    profileCode P = profileCode Q ↔ ∀ D, prefixResidual (deletedPrefix P D) = prefixResidual (deletedPrefix Q D) := by
  constructor
  · intro h D
    have he : profile P D = profile Q D := Fin.ext (congrArg (fun r : Fin 4 => r.val) (congrFun h D))
    rw [← profile_semantics,← profile_semantics,he]
  · intro h
    funext D
    apply congrArg embedKind
    exact residualLanguage_injective _ ((profile_semantics _ _).trans ((h D).trans (profile_semantics _ _).symm))

end CounterFreeHDA.Appendix.Residual
