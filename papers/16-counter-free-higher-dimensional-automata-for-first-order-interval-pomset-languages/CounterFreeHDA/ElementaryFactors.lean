import CounterFreeHDA.STRepresentation
import CounterFreeHDA.TerminationSize

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hw : P.WidthLE k)

/-- A start chosen from the actual interval order gives an elementary
factorization of smaller residual measure. -/
noncomputable def startFactor (e : Fin P.n) (he : P.Startable e) : PeelFactor (k := k) P := by
  classical
  let Q := SourceExpansion.residual P hP e he
  have hQ : IsIntervalPom Q := SourceExpansion.residual_wf P hP e he
  have hwQ : Q.WidthLE k := hw.ofEmbedding ⟨id,Function.injective_id⟩ (fun _ _ h => h)
  let U := sourceCube P (hw.source_bound hP)
  let V := targetCube P (hw.target_bound hP)
  let W := sourceCube Q (hwQ.source_bound hQ)
  let a : Fin U.dim ↪o Fin W.dim := SourceExpansion.embedding P hP e he
  have hl : ∀ i, W.lab (a i) = U.lab i := fun i => congrArg P.lab (SourceExpansion.position_spec P hP e he i)
  let f : Face U W := Face.ofEmbedding a hl false
  have hd : W.dim = U.dim + 1 := SourceExpansion.source_size P hP e he
  let s : Step U W := .start f (Face.ofEmbedding_lower a hl) hd
  have hi := SourceExpansion.iso P hP e he
  have htarget : Q.tgtType = P.tgtType := (glue_tgtType _).symm.trans hi.target_type
  let tail : Arrow W V := { pom := ⟨Q,hQ⟩,source := rfl,target := htarget }
  have hs : PomsetIso s.label.pom.val (StarterGlue.starter Q a).val := by
    change PomsetIso (discretePom W.lab f.positionEmbedding (OrderEmbedding.ofStrictMono id (fun _ _ h => h))).val
      (StarterGlue.starter Q a).val
    have hf : f.positionEmbedding = a := Face.ofEmbedding_positionEmbedding a hl false
    rw [hf]
    exact PomsetIso.refl _
  have hcomp := PomsetIso.glueIso hs (PomsetIso.refl Q)
    (GlueMatch.ofType (s.label.target.trans tail.source.symm)) (StarterGlue.matching Q a)
  have hsize : Q.n = P.n := rfl
  have hsource : Q.srcLen = P.srcLen + 1 := SourceExpansion.source_size P hP e he
  have htgt : Q.tgtLen = P.tgtLen := Reinterface.targetSet_card P
  have hbound := srcLen_le Q
  have hbound' := tgtLen_le P
  exact {
    sourceType := U,targetType := V,middleType := W,step := s,tail := tail
    iso := hcomp.trans hi
    width := hwQ
    decreases := by change 2 * Q.n - Q.srcLen - Q.tgtLen < 2 * P.n - P.srcLen - P.tgtLen; omega }

/-- A legal source termination gives an elementary factorization with one
fewer event and a strictly smaller residual measure. -/
noncomputable def stopFactor (i : Fin P.srcLen) (ht : ¬ P.inTgt (P.src i))
    (hc : ∀ e, ¬ P.inSrc e → P.prec (P.src i) e) : PeelFactor (k := k) P := by
  classical
  let Q := TerminatorGlue.residual P i ht
  have hQ : IsIntervalPom Q := Induced.isIntervalPom P (TerminatorGlue.keep P i) hP _ _ _ _
  have hwQ : Q.WidthLE k := hw.ofEmbedding (TerminatorGlue.inclusion P i ht) (fun _ _ h => h)
  let U := sourceCube P (hw.source_bound hP)
  let V := targetCube P (hw.target_bound hP)
  let W := sourceCube Q (hwQ.source_bound hQ)
  let a : Fin W.dim ↪o Fin U.dim := (TerminatorGlue.remaining P i).orderEmbOfFin rfl
  have hl : ∀ j, U.lab (a j) = W.lab j := by
    intro j
    exact (congrArg P.lab (TerminatorGlue.inclusion_source P i ht j)).symm
  let f : Face W U := Face.ofEmbedding a hl true
  have hd : U.dim = W.dim + 1 := (TerminatorGlue.remaining_size P i).symm
  let s : Step U W := .stop f (Face.ofEmbedding_upper a hl) hd
  have hi := TerminatorGlue.iso P i ht hP hc
  have htarget : Q.tgtType = P.tgtType := (glue_tgtType _).symm.trans hi.target_type
  let tail : Arrow W V := { pom := ⟨Q,hQ⟩,source := rfl,target := htarget }
  have hs : PomsetIso s.label.pom.val (TerminatorGlue.terminator P i).val := by
    change PomsetIso (discretePom U.lab (OrderEmbedding.ofStrictMono id (fun _ _ h => h)) f.positionEmbedding).val
      (TerminatorGlue.terminator P i).val
    have hf : f.positionEmbedding = a := Face.ofEmbedding_positionEmbedding a hl true
    rw [hf]
    exact PomsetIso.refl _
  have hcomp := PomsetIso.glueIso hs (PomsetIso.refl Q)
    (GlueMatch.ofType (s.label.target.trans tail.source.symm)) (TerminatorGlue.matching P i ht)
  have hsize : Q.n + 1 = P.n := TerminatorGlue.residual_size P i ht
  have hsource : Q.srcLen + 1 = P.srcLen := TerminatorGlue.remaining_size P i
  have htgt : Q.tgtLen = P.tgtLen := TerminatorGlue.residual_target_size P i ht
  have hbound := srcLen_le Q
  have hbound' := tgtLen_le Q
  exact {
    sourceType := U,targetType := V,middleType := W,step := s,tail := tail
    iso := hcomp.trans hi
    width := hwQ
    decreases := by change 2 * Q.n - Q.srcLen - Q.tgtLen < 2 * P.n - P.srcLen - P.tgtLen; omega }

end CounterFreeHDA.Cubical
