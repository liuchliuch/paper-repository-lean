import CounterFreeHDA.MiddleCorner

namespace CounterFreeHDA.EndoPom
universe u
open Cubical Cubical.TrackGlue
variable {Lab : Type u} {U : Interface Lab}

def sourceAt (P : EndoPom U) (i : Fin U.1) : Fin P.pom.n := P.pom.src (Fin.cast P.src_len.symm i)
def targetAt (P : EndoPom U) (i : Fin U.1) : Fin P.pom.n := P.pom.tgt (Fin.cast P.tgt_len.symm i)
def sourceStatus (P : EndoPom U) (f : Fin U.1 → Status) : Fin P.pom.srcLen → Status := fun i => f (Fin.cast P.src_len i)
def targetStatus (P : EndoPom U) (f : Fin U.1 → Status) : Fin P.pom.tgtLen → Status := fun i => f (Fin.cast P.tgt_len i)
noncomputable def mulMatch (P Q : EndoPom U) : GlueMatch P.pom.val Q.pom.val :=
  GlueMatch.ofType (P.target.trans Q.source.symm)

theorem mul_sourceAt (P Q : EndoPom U) (i : Fin U.1) :
    (P.mul Q).sourceAt i = leftEvent (P.mulMatch Q) (P.sourceAt i) := by
  exact congrArg (fun j => leftEvent (P.mulMatch Q) (P.pom.src j)) (Fin.ext rfl)

theorem mul_targetAt (P Q : EndoPom U) (i : Fin U.1) :
    (P.mul Q).targetAt i = rightEvent (P.mulMatch Q) (Q.targetAt i) := by
  exact congrArg (fun j => rightEvent (P.mulMatch Q) (Q.pom.tgt j)) (Fin.ext rfl)

theorem mul_seam (P Q : EndoPom U) (i : Fin U.1) :
    leftEvent (P.mulMatch Q) (P.targetAt i) = rightEvent (P.mulMatch Q) (Q.sourceAt i) := by
  exact (congrArg (index (P.mulMatch Q)) (GluedE.identified P.pom.val Q.pom.val (P.mulMatch Q).len_eq
    (Fin.cast P.tgt_len.symm i))).trans
      (congrArg (fun j => rightEvent (P.mulMatch Q) (Q.pom.src j)) (Fin.ext rfl))

theorem mul_overlap (P Q : EndoPom U) (e : Fin P.pom.n) (f : Fin Q.pom.n) :
    leftEvent (P.mulMatch Q) e = rightEvent (P.mulMatch Q) f ↔
      ∃ i : Fin U.1, P.targetAt i = e ∧ Q.sourceAt i = f := by
  simp only [leftEvent,rightEvent]
  rw [(index (P.mulMatch Q)).injective.eq_iff,glued_identified_iff]
  constructor
  · rintro ⟨i,hi,hj⟩
    refine ⟨Fin.cast P.tgt_len i,?_,?_⟩
    · simpa only [targetAt,Fin.cast_cast,Fin.cast_refl,id_eq] using hi
    · exact (congrArg Q.pom.src (Fin.ext rfl)).trans hj
  · rintro ⟨i,hi,hj⟩
    exact ⟨Fin.cast P.tgt_len.symm i,hi,(congrArg Q.pom.src (Fin.ext rfl)).trans hj⟩

theorem deleted_iff (P : EndoPom U) (f g : Fin U.1 → Status) (e : Fin P.pom.n) :
    Corners.Deleted P.pom.val (P.sourceStatus f) (P.targetStatus g) e ↔
      (∃ i, P.sourceAt i = e ∧ f i = Status.one) ∨ (∃ j, P.targetAt j = e ∧ g j = Status.zero) := by
  constructor
  · rintro (⟨i,hi,hf⟩ | ⟨i,hi,hg⟩)
    · refine Or.inl ⟨Fin.cast P.src_len i,?_,hf⟩
      simpa only [sourceAt,Fin.cast_cast,Fin.cast_refl,id_eq] using hi
    · refine Or.inr ⟨Fin.cast P.tgt_len i,?_,hg⟩
      simpa only [targetAt,Fin.cast_cast,Fin.cast_refl,id_eq] using hi
  · rintro (⟨i,hi,hf⟩ | ⟨i,hi,hg⟩)
    · refine Or.inl ⟨Fin.cast P.src_len.symm i,hi,?_⟩
      simpa only [sourceStatus,Fin.cast_cast,Fin.cast_refl,id_eq] using hf
    · refine Or.inr ⟨Fin.cast P.tgt_len.symm i,hi,?_⟩
      simpa only [targetStatus,Fin.cast_cast,Fin.cast_refl,id_eq] using hg

end CounterFreeHDA.EndoPom
