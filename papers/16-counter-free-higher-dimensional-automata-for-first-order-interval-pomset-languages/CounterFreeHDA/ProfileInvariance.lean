import CounterFreeHDA.LiveProfileTable
import CounterFreeHDA.TypedCornerIso

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem profile_iso {U : UCube} (P Q : Prefix U) (φ : PomsetIso P.pom.val Q.pom.val) : profile P = profile Q := by
  funext D
  apply residualLanguage_injective
  rw [profile_semantics,profile_semantics]
  exact prefixResidual_iso _ _ (P.toArrow.cornerIso Q.toArrow φ P.width Q.width _ _
    (empty_source_compatible P _) (empty_source_compatible Q _))

theorem profileCode_iso {U : UCube} (P Q : Prefix U) (φ : PomsetIso P.pom.val Q.pom.val) : profileCode P = profileCode Q := by
  unfold profileCode
  rw [profile_iso P Q φ]

theorem profileCode_append {U V : UCube} (P : Prefix U) (p : Word U V) :
    profileCode (P.comp (BoundedArrow.ofWord p)) =
      executeCode p (profileCode P) := by
  induction p with
  | nil U =>
    exact profileCode_iso _ _ P.identityRightIso
  | cons s p ih =>
    have he := profileCode_iso (P.comp ((BoundedArrow.ofStep s).comp (BoundedArrow.ofWord p)))
      ((P.comp (BoundedArrow.ofStep s)).comp (BoundedArrow.ofWord p))
      (BoundedArrow.assocIso P _ _).symm
    exact he.trans ((ih (P.comp (BoundedArrow.ofStep s))).trans
      (by rw [profileCode_update]; rfl))

/-- The identity prefix contains no events, and every deletion coordinate
is the actual initial suffix residual A. -/
theorem initial_profileCode : profileCode (BoundedArrow.ident Completion.emptyCube) = fun _ => (0 : Fin 4) := by
  funext D
  let Q := deletedPrefix (BoundedArrow.ident Completion.emptyCube) D
  have hn : Q.pom.n = 0 := by
    let I := BoundedArrow.ident Completion.emptyCube
    let α := I.toArrow.sourceFace (Cubical.Face.ident Completion.emptyCube)
    let β := I.toArrow.targetFace (deletionFace Completion.emptyCube D)
    let hc := I.toArrow.compatible_raw _ _ (empty_source_compatible I (deletionFace Completion.emptyCube D))
    let incl : Fin Q.pom.n ↪ Fin 0 := Corners.inclusion I.pom.val α.status β.status hc
    have hi := Fintype.card_le_of_injective incl incl.injective
    simp only [Fintype.card_fin] at hi
    change Q.pom.n ≤ 0 at hi
    omega
  have hl : Q.representative.length = 0 := by
    rw [← Q.representative.stMeasure_label,stMeasure_iso Q.representativeIso]
    unfold stMeasure
    change 2*Q.pom.n-Q.pom.srcLen-Q.pom.tgtLen = 0
    rw [hn]
    omega
  change embedKind (wordKind Q.representative (0 : Fin 4)) = _
  generalize hp : Q.representative = p at hl ⊢
  cases p with
  | nil => rfl
  | cons s p => change p.length+1 = 0 at hl; omega

end CounterFreeHDA.Appendix.Residual
