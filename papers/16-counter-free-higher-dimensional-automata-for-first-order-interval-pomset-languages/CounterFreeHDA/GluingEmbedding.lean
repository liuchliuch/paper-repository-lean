import CounterFreeHDA.GluingRealization

/-! Event embeddings of a gluing need exact seam overlap, even when the
ambient pomset contains events outside the represented path. -/
namespace CounterFreeHDA
universe u
variable {Lab : Type u} {A B P : PomsetData Lab}

structure GluingEmbedding (m : GlueMatch A B) (P : PomsetData Lab) where
  left : Fin A.n ↪ Fin P.n
  right : Fin B.n ↪ Fin P.n
  seam : ∀ i, left (A.tgt i) = right (B.src (Fin.cast m.len_eq i))
  overlap : ∀ e f, left e = right f → ∃ i, A.tgt i = e ∧ B.src (Fin.cast m.len_eq i) = f

namespace GluingEmbedding
variable {m : GlueMatch A B} (R : GluingEmbedding m P)

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

noncomputable def embedding : Fin (glueData A B m).n ↪ Fin P.n :=
  ⟨fun e => R.raw ((Cubical.TrackGlue.index m).symm e),
    R.raw_injective.comp (Cubical.TrackGlue.index m).symm.injective⟩

@[simp] theorem embedding_left (e : Fin A.n) :
    R.embedding (Cubical.TrackGlue.leftEvent m e) = R.left e := by
  change R.raw ((Cubical.TrackGlue.index m).symm ((Cubical.TrackGlue.index m) _)) = _
  rw [Equiv.symm_apply_apply,R.raw_left]

@[simp] theorem embedding_right (e : Fin B.n) :
    R.embedding (Cubical.TrackGlue.rightEvent m e) = R.right e := by
  change R.raw ((Cubical.TrackGlue.index m).symm ((Cubical.TrackGlue.index m) _)) = _
  rw [Equiv.symm_apply_apply,R.raw_right]

theorem range_iff (e : Fin P.n) :
    (∃ a, R.embedding a = e) ↔ (∃ a, R.left a = e) ∨ (∃ b, R.right b = e) := by
  constructor
  · rintro ⟨a,ha⟩
    change R.raw ((Cubical.TrackGlue.index m).symm a) = e at ha
    cases hh : (Cubical.TrackGlue.index m).symm a with
    | left a => rw [hh] at ha; exact Or.inl ⟨a.val,ha⟩
    | right a => rw [hh] at ha; exact Or.inr ⟨a.val,ha⟩
    | mid i => rw [hh] at ha; exact Or.inl ⟨A.tgt i,ha⟩
  · rintro (⟨a,rfl⟩ | ⟨b,rfl⟩)
    · exact ⟨Cubical.TrackGlue.leftEvent m a,R.embedding_left a⟩
    · exact ⟨Cubical.TrackGlue.rightEvent m b,R.embedding_right b⟩

end GluingEmbedding
end CounterFreeHDA
