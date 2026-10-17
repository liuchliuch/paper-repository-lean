import CounterFreeHDA.FaceStatuses
import CounterFreeHDA.EndpointCriterion

namespace CounterFreeHDA.Cubical.Arrow
universe u
variable {Lab : Type u} {k : ℕ} {U V T W : Cube Lab k}

/-- Pull an actual source face back to the pomset's raw ordered source. -/
noncomputable def sourceFace (A : Arrow U V) (α : Face T U) : Face T (sourceCube A.pom.val A.source_bound) where
  sub j := α.sub (Fin.cast A.src_len j)
  vars i := by
    obtain ⟨j,hj,hu⟩ := α.vars i
    refine ⟨Fin.cast A.src_len.symm j,?_,?_⟩
    · simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj
    · intro l hl
      exact Fin.ext (congrArg (fun x : Fin U.dim => x.val) (hu (Fin.cast A.src_len l) hl))
  ordered hij hi hj := α.ordered hij hi hj
  labels := by
    intro j i h
    have he := A.source_label (Fin.cast A.src_len j)
    have hl : A.pom.lab (A.pom.src j) = U.lab (Fin.cast A.src_len j) := by
      simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using he
    exact hl.trans (α.labels h)

/-- Pull an actual target face back to the pomset's raw ordered target. -/
noncomputable def targetFace (A : Arrow U V) (β : Face W V) : Face W (targetCube A.pom.val A.target_bound) where
  sub j := β.sub (Fin.cast A.tgt_len j)
  vars i := by
    obtain ⟨j,hj,hu⟩ := β.vars i
    refine ⟨Fin.cast A.tgt_len.symm j,?_,?_⟩
    · simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hj
    · intro l hl
      exact Fin.ext (congrArg (fun x : Fin V.dim => x.val) (hu (Fin.cast A.tgt_len l) hl))
  ordered hij hi hj := β.ordered hij hi hj
  labels := by
    intro j i h
    have he := A.target_label (Fin.cast A.tgt_len j)
    have hl : A.pom.lab (A.pom.tgt j) = V.lab (Fin.cast A.tgt_len j) := by
      simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using he
    exact hl.trans (β.labels h)

@[simp] theorem sourceFace_status (A : Arrow U V) (α : Face T U) (i : Fin A.pom.srcLen) :
    (A.sourceFace α).status i = α.status (Fin.cast A.src_len i) := rfl

@[simp] theorem targetFace_status (A : Arrow U V) (β : Face W V) (i : Fin A.pom.tgtLen) :
    (A.targetFace β).status i = β.status (Fin.cast A.tgt_len i) := rfl

def Compatible (A : Arrow U V) (α : Face T U) (β : Face W V) : Prop :=
  ∀ i j, A.pom.src (Fin.cast A.src_len.symm i) = A.pom.tgt (Fin.cast A.tgt_len.symm j) → α.status i ≤ β.status j

theorem compatible_raw (A : Arrow U V) (α : Face T U) (β : Face W V) (hc : A.Compatible α β) :
    Corners.Compatible A.pom.val (A.sourceFace α).status (A.targetFace β).status := by
  intro i j hij
  apply hc (Fin.cast A.src_len i) (Fin.cast A.tgt_len j)
  simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hij

noncomputable def corner (A : Arrow U V) (hw : A.pom.val.WidthLE k)
    (α : Face T U) (β : Face W V) (hc : A.Compatible α β) : BoundedArrow T W :=
  CornerFaces.boundedArrow A.pom.val A.pom.property hw A.source_bound A.target_bound
    (A.sourceFace α) (A.targetFace β) (A.compatible_raw α β hc)

end CounterFreeHDA.Cubical.Arrow
