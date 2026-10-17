import CounterFreeHDA.GluingAtlas
import CounterFreeHDA.CornerInterfaces

namespace CounterFreeHDA.Corners
universe u
open Cubical.TrackGlue
variable {Lab : Type u} {A B : PomsetData Lab} (m : GlueMatch A B)
    (α : Fin A.srcLen → Status) (γ : Fin A.tgtLen → Status) (β : Fin B.tgtLen → Status)

abbrev seamStatus : Fin B.srcLen → Status := fun i => γ (Fin.cast m.len_eq.symm i)

variable (ha : Compatible A α γ) (hb : Compatible B (seamStatus m γ) β)
    (hg : Compatible (glueData A B m) α β)
    (hl : ∀ e, Deleted (glueData A B m) α β (leftEvent m e) ↔ Deleted A α γ e)
    (hr : ∀ e, Deleted (glueData A B m) α β (rightEvent m e) ↔ Deleted B (seamStatus m γ) β e)

include ha hb in
theorem compatible_glue : Compatible (glueData A B m) α β := by
  intro i j hij
  obtain ⟨l,hil,hlj⟩ := (glue_shared_iff m i j).mp hij
  exact (ha i l hil).trans (hb (Fin.cast m.len_eq l) j hlj)

noncomputable def gluingPlan : Deletion.Plan m := by
  classical
  exact {
    keepA := fun e => ¬ Deleted A α γ e
    keepB := fun e => ¬ Deleted B (seamStatus m γ) β e
    keepG := fun e => ¬ Deleted (glueData A B m) α β e
    left_iff := fun e => (hl e).not
    right_iff := fun e => (hr e).not }

/-- Restrict a real event gluing to compatible corners. The hypotheses state
which original events survive; all orders, overlap and interfaces are derived. -/
noncomputable def gluingAtlas (hA : IsIntervalPom A) (hB : IsIntervalPom B)
    (hγ : ∀ i, ¬ Deleted A α γ (A.tgt i) → γ i = Status.star) :
    GluingAtlas (data A α γ ha) (data B (seamStatus m γ) β hb)
      (data (glueData A B m) α β hg) := by
  classical
  let D := gluingPlan m α γ β hl hr
  let R := D.realization hA hB
  have ht : ∀ e, (data A α γ ha).inTgt e ↔ D.leftData.inTgt e := by
    intro e
    refine (target_iff A α γ ha e).trans ?_
    rw [Deletion.inTgt_iff]
    constructor
    · rintro ⟨i,hi,_⟩; exact ⟨i,hi⟩
    · rintro ⟨i,hi⟩
      exact ⟨i,hi,hγ i (hi.symm ▸ inclusion_kept A α γ ha e)⟩
  have hs : ∀ e, (data B (seamStatus m γ) β hb).inSrc e ↔ D.rightData.inSrc e := by
    intro e
    refine (source_iff B (seamStatus m γ) β hb e).trans ?_
    rw [Deletion.inSrc_iff]
    constructor
    · rintro ⟨i,hi,_⟩; exact ⟨i,hi⟩
    · rintro ⟨i,hi⟩
      have hk : D.keepB (B.src i) := hi.symm ▸ inclusion_kept B (seamStatus m γ) β hb e
      have hkA := (D.seam_kept (Fin.cast m.len_eq.symm i)).mpr
        (by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hk)
      exact ⟨i,hi,hγ _ hkA⟩
  have hsource : ∀ e, (data (glueData A B m) α β hg).inSrc (D.left e) ↔ (data A α γ ha).inSrc e := by
    intro e
    rw [source_iff,source_iff]
    constructor
    · rintro ⟨i,hi,hα⟩
      have he : A.src i = inclusion A α γ ha e :=
        ((index m).injective.comp (GluedE.leftMap_inj A B)) (hi.trans (D.inclusion_left e))
      exact ⟨i,he,hα⟩
    · rintro ⟨i,hi,hα⟩
      exact ⟨i,(congrArg (leftEvent m) hi).trans (D.inclusion_left e).symm,hα⟩
  have htarget : ∀ e, (data (glueData A B m) α β hg).inTgt (D.right e) ↔
      (data B (seamStatus m γ) β hb).inTgt e := by
    intro e
    rw [target_iff,target_iff]
    constructor
    · rintro ⟨i,hi,hβ⟩
      have he : B.tgt i = inclusion B (seamStatus m γ) β hb e :=
        ((index m).injective.comp (GluedE.rightMap_inj A B m.len_eq)) (hi.trans (D.inclusion_right e))
      exact ⟨i,he,hβ⟩
    · rintro ⟨i,hi,hβ⟩
      exact ⟨i,(congrArg (rightEvent m) hi).trans (D.inclusion_right e).symm,hβ⟩
  refine {
    left := D.left,right := D.right,left_lab := R.left_lab,right_lab := R.right_lab
    left_prec := R.left_prec,right_prec := R.right_prec,left_eord := R.left_eord,right_eord := R.right_eord
    cover := R.cover
    cross := fun e f he hf => R.cross e f (fun h => he ((ht e).mpr h)) (fun h => hf ((hs f).mpr h))
    overlap := ?_
    seam_range := ?_
    source_range := ?_
    target_range := ?_ }
  · have ha' : Set.range (data A α γ ha).tgt = Set.range D.leftData.tgt := Set.ext ht
    have hb' : Set.range (data B (seamStatus m γ) β hb).src = Set.range D.rightData.src := Set.ext hs
    simpa only [Set.range_comp,ha',hb'] using R.atlas.seam_range
  · intro e f hef
    obtain ⟨i,hi,hj⟩ := R.overlap e f hef
    exact ⟨(ht e).mpr ⟨i,hi⟩,(hs f).mpr ⟨_,hj⟩⟩
  · ext e
    constructor
    · rintro ⟨i,rfl⟩
      exact (hsource _).mpr ⟨i,rfl⟩
    · intro he
      obtain ⟨i,hi,hα⟩ := (source_iff (glueData A B m) α β hg e).mp he
      have hgsrc : D.gluedData.inSrc e := (Deletion.inSrc_iff _ _ e).mpr ⟨i,hi⟩
      obtain ⟨j,hj⟩ := (Set.ext_iff.mp R.atlas.source_range e).mpr hgsrc
      change D.left (D.leftData.src j) = e at hj
      obtain ⟨l,hl'⟩ := (hsource (D.leftData.src j)).mp (hj.symm ▸ he)
      exact ⟨l,(congrArg D.left hl').trans hj⟩
  · ext e
    constructor
    · rintro ⟨i,rfl⟩
      exact (htarget _).mpr ⟨i,rfl⟩
    · intro he
      obtain ⟨i,hi,hβ⟩ := (target_iff (glueData A B m) α β hg e).mp he
      have hgtgt : D.gluedData.inTgt e := (Deletion.inTgt_iff _ _ e).mpr ⟨i,hi⟩
      obtain ⟨j,hj⟩ := (Set.ext_iff.mp R.atlas.target_range e).mpr hgtgt
      change D.right (D.rightData.tgt j) = e at hj
      obtain ⟨l,hl'⟩ := (htarget (D.rightData.tgt j)).mp (hj.symm ▸ he)
      exact ⟨l,(congrArg D.right hl').trans hj⟩

end CounterFreeHDA.Corners
