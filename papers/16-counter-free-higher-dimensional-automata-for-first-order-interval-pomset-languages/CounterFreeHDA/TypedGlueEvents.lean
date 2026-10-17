import CounterFreeHDA.TypedCornerInterfaces
import CounterFreeHDA.Shared

namespace CounterFreeHDA.Cubical.Arrow
universe u
open TrackGlue
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

def sourceEvent (A : Arrow U V) (i : Fin U.dim) : Fin A.pom.n := A.pom.src (Fin.cast A.src_len.symm i)
def targetEvent (A : Arrow U V) (i : Fin V.dim) : Fin A.pom.n := A.pom.tgt (Fin.cast A.tgt_len.symm i)
noncomputable def matching (A : Arrow U V) (B : Arrow V W) : GlueMatch A.pom.val B.pom.val :=
  GlueMatch.ofType (A.target.trans B.source.symm)

theorem comp_sourceEvent (A : Arrow U V) (B : Arrow V W) (i : Fin U.dim) :
    (A.comp B).sourceEvent i = leftEvent (A.matching B) (A.sourceEvent i) :=
  congrArg (fun j => leftEvent (A.matching B) (A.pom.src j)) (Fin.ext rfl)

theorem comp_targetEvent (A : Arrow U V) (B : Arrow V W) (i : Fin W.dim) :
    (A.comp B).targetEvent i = rightEvent (A.matching B) (B.targetEvent i) :=
  congrArg (fun j => rightEvent (A.matching B) (B.pom.tgt j)) (Fin.ext rfl)

theorem seam_event (A : Arrow U V) (B : Arrow V W) (i : Fin V.dim) :
    leftEvent (A.matching B) (A.targetEvent i) = rightEvent (A.matching B) (B.sourceEvent i) :=
  (congrArg (index (A.matching B)) (GluedE.identified A.pom.val B.pom.val (A.matching B).len_eq
    (Fin.cast A.tgt_len.symm i))).trans
      (congrArg (fun j => rightEvent (A.matching B) (B.pom.src j)) (Fin.ext rfl))

theorem event_overlap (A : Arrow U V) (B : Arrow V W) (e : Fin A.pom.n) (f : Fin B.pom.n) :
    leftEvent (A.matching B) e = rightEvent (A.matching B) f ↔
      ∃ i : Fin V.dim, A.targetEvent i = e ∧ B.sourceEvent i = f := by
  simp only [leftEvent,rightEvent]
  rw [(index (A.matching B)).injective.eq_iff,glued_identified_iff]
  constructor
  · rintro ⟨i,hi,hj⟩
    refine ⟨Fin.cast A.tgt_len i,?_,?_⟩
    · simpa only [targetEvent,Fin.cast_cast,Fin.cast_refl,id_eq] using hi
    · exact (congrArg B.pom.src (Fin.ext rfl)).trans hj
  · rintro ⟨i,hi,hj⟩
    exact ⟨Fin.cast A.tgt_len.symm i,hi,(congrArg B.pom.src (Fin.ext rfl)).trans hj⟩

end CounterFreeHDA.Cubical.Arrow
