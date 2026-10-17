import CounterFreeHDA.GluingIso

/-! A concrete universal property for event gluing. The witnesses below are
embeddings into one actual pomset, with exact overlap and cross precedence. -/
namespace CounterFreeHDA
universe u
variable {Lab : Type u} {A B P : PomsetData Lab}

structure GluingRealization (m : GlueMatch A B) (P : PomsetData Lab) where
  left : Fin A.n ↪ Fin P.n
  right : Fin B.n ↪ Fin P.n
  left_lab : ∀ e, P.lab (left e) = A.lab e
  right_lab : ∀ e, P.lab (right e) = B.lab e
  left_prec : ∀ e f, P.prec (left e) (left f) ↔ A.prec e f
  right_prec : ∀ e f, P.prec (right e) (right f) ↔ B.prec e f
  left_eord : ∀ e f, P.eord (left e) (left f) ↔ A.eord e f
  right_eord : ∀ e f, P.eord (right e) (right f) ↔ B.eord e f
  seam : ∀ i, left (A.tgt i) = right (B.src (Fin.cast m.len_eq i))
  overlap : ∀ e f, left e = right f → ∃ i, A.tgt i = e ∧ B.src (Fin.cast m.len_eq i) = f
  cover : ∀ e, (∃ a, left a = e) ∨ (∃ b, right b = e)
  cross : ∀ e f, ¬ A.inTgt e → ¬ B.inSrc f → P.prec (left e) (right f)
  source_len : A.srcLen = P.srcLen
  target_len : B.tgtLen = P.tgtLen
  source : ∀ i, left (A.src i) = P.src (Fin.cast source_len i)
  target : ∀ i, right (B.tgt i) = P.tgt (Fin.cast target_len i)

namespace GluingRealization
variable {m : GlueMatch A B} (R : GluingRealization m P)

def raw : GluedE A B → Fin P.n
  | .left e => R.left e.val
  | .right e => R.right e.val
  | .mid i => R.left (A.tgt i)

theorem raw_left (e : Fin A.n) : R.raw (GluedE.leftMap A B e) = R.left e := by
  classical
  unfold GluedE.leftMap
  split_ifs with he
  · change R.left (A.tgt (Classical.choose he)) = R.left e
    rw [Classical.choose_spec he]
  · rfl

theorem raw_right (e : Fin B.n) : R.raw (GluedE.rightMap A B m.len_eq e) = R.right e := by
  classical
  unfold GluedE.rightMap
  split_ifs with he
  · change R.left (A.tgt (Fin.cast m.len_eq.symm (Classical.choose he))) = R.right e
    rw [R.seam]
    simp only [Fin.cast_cast,Fin.cast_refl,id_eq,Classical.choose_spec he]
  · rfl

theorem raw_injective : Function.Injective R.raw := by
  intro e f h
  cases e with
  | left e =>
    cases f with
    | left f => exact congrArg GluedE.left (Subtype.ext (R.left.injective h))
    | right f => obtain ⟨i,hi,_⟩ := R.overlap e.val f.val h; exact False.elim (e.property ⟨i,hi⟩)
    | mid i => exact False.elim (e.property ⟨i,(R.left.injective h).symm⟩)
  | right e =>
    cases f with
    | left f => obtain ⟨i,hi,_⟩ := R.overlap f.val e.val h.symm; exact False.elim (f.property ⟨i,hi⟩)
    | right f => exact congrArg GluedE.right (Subtype.ext (R.right.injective h))
    | mid i =>
      change R.right e.val = R.left (A.tgt i) at h
      rw [R.seam] at h
      exact False.elim (e.property ⟨Fin.cast m.len_eq i,(R.right.injective h).symm⟩)
  | mid i =>
    cases f with
    | left f => exact False.elim (f.property ⟨i,R.left.injective h⟩)
    | right f =>
      change R.left (A.tgt i) = R.right f.val at h
      rw [R.seam] at h
      exact False.elim (f.property ⟨Fin.cast m.len_eq i,R.right.injective h⟩)
    | mid j => exact congrArg GluedE.mid (A.tgt_inj (R.left.injective h))

theorem raw_surjective : Function.Surjective R.raw := by
  intro e
  rcases R.cover e with ⟨a,rfl⟩ | ⟨b,rfl⟩
  · exact ⟨GluedE.leftMap A B a,R.raw_left a⟩
  · exact ⟨GluedE.rightMap A B m.len_eq b,R.raw_right b⟩

noncomputable def rawEquiv : GluedE A B ≃ Fin P.n :=
  Equiv.ofBijective R.raw ⟨R.raw_injective,R.raw_surjective⟩

theorem raw_lab (e : GluedE A B) : P.lab (R.raw e) = glueLab m e := by
  cases e with
  | left e => exact R.left_lab e.val
  | right e => exact R.right_lab e.val
  | mid i => exact R.left_lab (A.tgt i)

variable (hA : IsIntervalPom A) (hB : IsIntervalPom B) (hP : IsIntervalPom P)

include hP in
private theorem cross_exclusion (e : Fin A.n) (f : Fin B.n)
    (he : ¬ A.inTgt e) (hf : ¬ B.inSrc f) :
    ¬ P.prec (R.right f) (R.left e) ∧ ¬ P.eord (R.left e) (R.right f) ∧
      ¬ P.eord (R.right f) (R.left e) := by
  have hp := R.cross e f he hf
  have hn : R.left e ≠ R.right f := by
    intro h
    rw [h] at hp
    exact hP.prec_irrefl _ hp
  exact (hP.trichotomy _ _ hn).2.1 hp

include hA hB hP in
theorem raw_prec (e f : GluedE A B) :
    P.prec (R.raw e) (R.raw f) ↔ gluePrec m.len_eq e f := by
  cases e with
  | left e =>
    cases f with
    | left f => exact R.left_prec e.val f.val
    | right f => exact iff_true_intro (R.cross _ _ e.property f.property)
    | mid i => exact R.left_prec e.val (A.tgt i)
  | right e =>
    cases f with
    | left f => exact iff_false_intro (cross_exclusion R hP _ _ f.property e.property).1
    | right f => exact R.right_prec e.val f.val
    | mid i =>
      change P.prec (R.right e.val) (R.left (A.tgt i)) ↔ False
      rw [R.seam,R.right_prec]
      exact iff_false_intro (hB.src_minimal _ ⟨_,rfl⟩ e.val)
  | mid i =>
    cases f with
    | left f =>
      change P.prec (R.left (A.tgt i)) (R.left f.val) ↔ False
      rw [R.left_prec]
      exact iff_false_intro (hA.tgt_maximal _ ⟨i,rfl⟩ f.val)
    | right f =>
      change P.prec (R.left (A.tgt i)) (R.right f.val) ↔ _
      rw [R.seam]
      exact R.right_prec _ _
    | mid j =>
      change P.prec (R.left (A.tgt i)) (R.left (A.tgt j)) ↔ False
      rw [R.left_prec]
      exact iff_false_intro (hA.tgt_maximal _ ⟨i,rfl⟩ _)

include hP in
theorem raw_eord (e f : GluedE A B) :
    P.eord (R.raw e) (R.raw f) ↔ glueEord m.len_eq e f := by
  cases e with
  | left e =>
    cases f with
    | left f => exact R.left_eord e.val f.val
    | right f => exact iff_false_intro (cross_exclusion R hP _ _ e.property f.property).2.1
    | mid i => exact R.left_eord e.val (A.tgt i)
  | right e =>
    cases f with
    | left f => exact iff_false_intro (cross_exclusion R hP _ _ f.property e.property).2.2
    | right f => exact R.right_eord e.val f.val
    | mid i =>
      change P.eord (R.right e.val) (R.left (A.tgt i)) ↔ _
      rw [R.seam]
      exact R.right_eord _ _
  | mid i =>
    cases f with
    | left f => exact R.left_eord (A.tgt i) f.val
    | right f =>
      change P.eord (R.left (A.tgt i)) (R.right f.val) ↔ _
      rw [R.seam]
      exact R.right_eord _ _
    | mid j => exact R.left_eord (A.tgt i) (A.tgt j)

/-- Exact cover, exact overlap, and the cross precedence identify the actual
pomset gluing with the represented pomset. -/
noncomputable def iso : PomsetIso (glueData A B m) P where
  toEquiv := (Fintype.equivFin (GluedE A B)).symm.trans R.rawEquiv
  lab_eq e := R.raw_lab _
  srcEquiv := finCongr R.source_len
  tgtEquiv := finCongr R.target_len
  src_mono _ _ := Iff.rfl
  tgt_mono _ _ := Iff.rfl
  src_eq i := by
    change R.raw ((Fintype.equivFin (GluedE A B)).symm
      ((Fintype.equivFin (GluedE A B)) (GluedE.leftMap A B (A.src i)))) = _
    rw [Equiv.symm_apply_apply,R.raw_left]
    exact R.source i
  tgt_eq i := by
    change R.raw ((Fintype.equivFin (GluedE A B)).symm
      ((Fintype.equivFin (GluedE A B)) (GluedE.rightMap A B m.len_eq (B.tgt i)))) = _
    rw [Equiv.symm_apply_apply,R.raw_right]
    exact R.target i
  prec_iff e f := R.raw_prec hA hB hP _ _
  eord_iff e f := R.raw_eord hP _ _

end GluingRealization
end CounterFreeHDA
