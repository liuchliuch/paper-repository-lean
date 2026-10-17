import CounterFreeHDA.TypedCorners

namespace CounterFreeHDA.Cubical.Arrow
universe u
variable {Lab : Type u} {k : ℕ} {U V T W : Cube Lab k}

theorem sourceFace_position (A : Arrow U V) (α : Face T U) (i : Fin T.dim) :
    (A.sourceFace α).position i = Fin.cast A.src_len.symm (α.position i) := by
  apply Eq.symm
  apply (A.sourceFace α).position_unique
  change α.sub (Fin.cast A.src_len (Fin.cast A.src_len.symm (α.position i))) = Sum.inl i
  simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using α.position_spec i

theorem targetFace_position (A : Arrow U V) (β : Face W V) (i : Fin W.dim) :
    (A.targetFace β).position i = Fin.cast A.tgt_len.symm (β.position i) := by
  apply Eq.symm
  apply (A.targetFace β).position_unique
  change β.sub (Fin.cast A.tgt_len (Fin.cast A.tgt_len.symm (β.position i))) = Sum.inl i
  simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using β.position_spec i

theorem corner_source (A : Arrow U V) (hw : A.pom.val.WidthLE k) (α : Face T U) (β : Face W V)
    (hc : A.Compatible α β) (i : Fin T.dim) :
    Corners.inclusion A.pom.val (A.sourceFace α).status (A.targetFace β).status (A.compatible_raw α β hc)
      ((A.corner hw α β hc).pom.src (Fin.cast (A.corner hw α β hc).toArrow.src_len.symm i)) =
        A.pom.src (Fin.cast A.src_len.symm (α.position i)) := by
  let f := A.sourceFace α
  let C := A.corner hw α β hc
  let j : Fin f.activePositions.card := Fin.cast C.toArrow.src_len.symm i
  have he := Corners.inclusion_source A.pom.val f.status (A.targetFace β).status (A.compatible_raw α β hc) j
  have hp := f.activePositions_orderEmb j
  have hj : Fin.cast f.activePositions_card j = i := Fin.ext rfl
  exact he.trans ((congrArg A.pom.src (hp.trans (congrArg f.position hj))).trans
    (congrArg A.pom.src (A.sourceFace_position α i)))

theorem corner_target (A : Arrow U V) (hw : A.pom.val.WidthLE k) (α : Face T U) (β : Face W V)
    (hc : A.Compatible α β) (i : Fin W.dim) :
    Corners.inclusion A.pom.val (A.sourceFace α).status (A.targetFace β).status (A.compatible_raw α β hc)
      ((A.corner hw α β hc).pom.tgt (Fin.cast (A.corner hw α β hc).toArrow.tgt_len.symm i)) =
        A.pom.tgt (Fin.cast A.tgt_len.symm (β.position i)) := by
  let f := A.targetFace β
  let C := A.corner hw α β hc
  let j : Fin f.activePositions.card := Fin.cast C.toArrow.tgt_len.symm i
  have he := Corners.inclusion_target A.pom.val (A.sourceFace α).status f.status (A.compatible_raw α β hc) j
  have hp := f.activePositions_orderEmb j
  have hj : Fin.cast f.activePositions_card j = i := Fin.ext rfl
  exact he.trans ((congrArg A.pom.tgt (hp.trans (congrArg f.position hj))).trans
    (congrArg A.pom.tgt (A.targetFace_position β i)))

end CounterFreeHDA.Cubical.Arrow
