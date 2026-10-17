import CounterFreeHDA.EndoBoundaryEvents

namespace CounterFreeHDA.EndoPom
universe u
open Cubical.TrackGlue
variable {Lab : Type u} {U : Interface Lab}
    (P Q : EndoPom U) (f g h : Fin U.1 → Status)

/-- Zero assignments reaching the left factor are exactly its prescribed
zero seam assignments. This is an event statement, including seam overlap. -/
theorem deleted_left
    (hleft : ∀ i j, Q.Shared i j → h j = Status.zero → g i = Status.zero)
    (hzero : ∀ i, g i = Status.zero → Q.Shared i i ∧ h i = Status.zero)
    (e : Fin P.pom.n) :
    Corners.Deleted (P.mul Q).pom.val ((P.mul Q).sourceStatus f) ((P.mul Q).targetStatus h)
      (leftEvent (P.mulMatch Q) e) ↔ Corners.Deleted P.pom.val (P.sourceStatus f) (P.targetStatus g) e := by
  refine ((P.mul Q).deleted_iff f h _).trans (Iff.trans ?_ (P.deleted_iff f g e).symm)
  constructor
  · rintro (⟨i,hi,hf⟩ | ⟨j,hj,hh⟩)
    · exact Or.inl ⟨i,((index (P.mulMatch Q)).injective.comp (GluedE.leftMap_inj _ _))
        ((P.mul_sourceAt Q i).symm.trans hi),hf⟩
    · obtain ⟨i,hi,hij⟩ := (P.mul_overlap Q e (Q.targetAt j)).mp
        (hj.symm.trans (P.mul_targetAt Q j))
      exact Or.inr ⟨i,hi,hleft i j hij hh⟩
  · rintro (⟨i,hi,hf⟩ | ⟨i,hi,hg⟩)
    · exact Or.inl ⟨i,(P.mul_sourceAt Q i).trans (congrArg (leftEvent (P.mulMatch Q)) hi),hf⟩
    · obtain ⟨hii,hh⟩ := hzero i hg
      exact Or.inr ⟨i,(P.mul_targetAt Q i).trans
        ((congrArg (rightEvent (P.mulMatch Q)) hii.symm).trans
          ((P.mul_seam Q i).symm.trans (congrArg (leftEvent (P.mulMatch Q)) hi))),hh⟩

theorem deleted_right
    (hright : ∀ i j, P.Shared i j → f i = Status.one → g j = Status.one)
    (hone : ∀ i, g i = Status.one → P.Shared i i ∧ f i = Status.one)
    (e : Fin Q.pom.n) :
    Corners.Deleted (P.mul Q).pom.val ((P.mul Q).sourceStatus f) ((P.mul Q).targetStatus h)
      (rightEvent (P.mulMatch Q) e) ↔ Corners.Deleted Q.pom.val (Q.sourceStatus g) (Q.targetStatus h) e := by
  refine ((P.mul Q).deleted_iff f h _).trans (Iff.trans ?_ (Q.deleted_iff g h e).symm)
  constructor
  · rintro (⟨i,hi,hf⟩ | ⟨i,hi,hh⟩)
    · obtain ⟨j,hij,hj⟩ := (P.mul_overlap Q (P.sourceAt i) e).mp ((P.mul_sourceAt Q i).symm.trans hi)
      exact Or.inl ⟨j,hj,hright i j hij.symm hf⟩
    · exact Or.inr ⟨i,((index (P.mulMatch Q)).injective.comp (GluedE.rightMap_inj _ _ _))
        ((P.mul_targetAt Q i).symm.trans hi),hh⟩
  · rintro (⟨i,hi,hg⟩ | ⟨i,hi,hh⟩)
    · obtain ⟨hii,hf⟩ := hone i hg
      exact Or.inl ⟨i,(P.mul_sourceAt Q i).trans ((congrArg (leftEvent (P.mulMatch Q)) hii).trans
        ((P.mul_seam Q i).trans (congrArg (rightEvent (P.mulMatch Q)) hi))),hf⟩
    · exact Or.inr ⟨i,(P.mul_targetAt Q i).trans (congrArg (rightEvent (P.mulMatch Q)) hi),hh⟩

theorem retained_seam_star (hc : Corners.Compatible P.pom.val (P.sourceStatus f) (P.targetStatus g))
    (hone : ∀ i, g i = Status.one → P.Shared i i ∧ f i = Status.one)
    (i : Fin P.pom.tgtLen)
    (hi : ¬ Corners.Deleted P.pom.val (P.sourceStatus f) (P.targetStatus g) (P.pom.tgt i)) :
    P.targetStatus g i = Status.star := by
  let j := Fin.cast P.tgt_len i
  have hzero : g j ≠ Status.zero := fun hz => hi (Or.inr ⟨i,rfl,hz⟩)
  have hone' : g j ≠ Status.one := by
    intro ho
    obtain ⟨hjj,hf⟩ := hone j ho
    apply hi
    apply (P.deleted_iff f g _).mpr
    exact Or.inl ⟨j,hjj.trans (congrArg P.pom.tgt (Fin.ext rfl)),hf⟩
  apply Fin.ext
  have hb := (g j).isLt
  have hz : (g j).val ≠ 0 := fun he => hzero (Fin.ext he)
  have ho : (g j).val ≠ 2 := fun he => hone' (Fin.ext he)
  change (g j).val = 1
  omega

end CounterFreeHDA.EndoPom
