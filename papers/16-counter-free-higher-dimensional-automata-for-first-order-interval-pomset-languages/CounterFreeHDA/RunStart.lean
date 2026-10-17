import CounterFreeHDA.TrackEventLemmas

namespace CounterFreeHDA.Cubical.RunLabeling
universe u
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab}
    {U V W : Cube Lab k}

/-- Prefixing a start creates no new event beyond those already present at
the source of the residual label; actual interface gluing identifies them. -/
noncomputable def start (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1)
    (p : Word V W) (z : TrackCell P V) (y : TrackCell P W)
    (R : RunLabeling p z y) : RunLabeling (.cons (.start f hl hd) p) (z.face f) y := by
  classical
  let s : Step U V := .start f hl hd
  let A := s.label
  let B := p.label
  let q : Word U W := .cons s p
  let m := GlueMatch.ofType (A.target.trans B.source.symm)
  have hfull : ∀ e, A.pom.val.inTgt e := fun e => ⟨e,rfl⟩
  let E := TrackGlue.rightEquiv m hfull
  have hsrc : ∀ i : Fin U.dim,
      E (B.pom.src (Fin.cast B.src_len.symm (f.position i))) = q.label.pom.src i := by
    intro i
    change TrackGlue.index m (GluedE.rightMap A.pom.val B.pom.val m.len_eq
      (B.pom.src (Fin.cast B.src_len.symm (f.position i)))) =
      TrackGlue.index m (GluedE.leftMap A.pom.val B.pom.val (f.position i))
    apply congrArg (TrackGlue.index m)
    have hr := GluedE.rightMap_src A.pom.val B.pom.val m.len_eq
      (Fin.cast B.src_len.symm (f.position i))
    have he : GluedE.leftMap A.pom.val B.pom.val (f.position i) = .mid (f.position i) :=
      GluedE.leftMap_tgt A.pom.val B.pom.val (f.position i)
    exact hr.trans ((congrArg GluedE.mid (Fin.ext rfl)).trans he.symm)
  exact {
    event := ⟨fun e => R.event (E.symm e),R.event.injective.comp E.symm.injective⟩
    labels e := by
      obtain ⟨a,rfl⟩ := E.surjective e
      change P.lab (R.event (E.symm (E a))) = _
      rw [Equiv.symm_apply_apply]
      exact (R.labels a).trans (TrackGlue.rightEvent_lab m a).symm
    source i := by
      change R.event (E.symm (q.label.pom.src i)) = z.occ (f.position i)
      rw [← hsrc i,Equiv.symm_apply_apply]
      exact (R.source _).trans (congrArg z.occ (Fin.ext rfl))
    target i := by
      change R.event (E.symm (E (B.pom.tgt i))) = y.occ _
      rw [Equiv.symm_apply_apply]
      exact R.target i
    support e := by
      have hrange : (∃ a, R.event (E.symm a) = e) ↔ ∃ b, R.event b = e := by
        constructor
        · rintro ⟨a,ha⟩; exact ⟨E.symm a,ha⟩
        · rintro ⟨b,hb⟩; exact ⟨E b,by simpa only [Equiv.symm_apply_apply] using hb⟩
      change (∃ a, R.event (E.symm a) = e) ↔ _
      rw [hrange,R.support]
      exact and_congr (TrackCell.lower_one_iff f hl z e).not.symm Iff.rfl
    precedence e g h := by
      obtain ⟨a,rfl⟩ := E.surjective e
      obtain ⟨b,rfl⟩ := E.surjective g
      change P.prec (R.event (E.symm (E a))) (R.event (E.symm (E b))) at h
      rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply] at h
      exact (TrackGlue.rightEvent_prec m B.pom.property a b).mpr (R.precedence a b h)
    order e g heg hge := by
      obtain ⟨a,rfl⟩ := E.surjective e
      obtain ⟨b,rfl⟩ := E.surjective g
      have hab : ¬ B.pom.prec a b := fun h => heg ((TrackGlue.rightEvent_prec m B.pom.property a b).mpr h)
      have hba : ¬ B.pom.prec b a := fun h => hge ((TrackGlue.rightEvent_prec m B.pom.property b a).mpr h)
      change q.label.pom.eord (E a) (E b) ↔ P.eord (R.event (E.symm (E a))) (R.event (E.symm (E b)))
      rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
      exact (TrackGlue.rightEvent_eord m A.pom.property B.pom.property a b).trans (R.order a b hab hba) }

end CounterFreeHDA.Cubical.RunLabeling
