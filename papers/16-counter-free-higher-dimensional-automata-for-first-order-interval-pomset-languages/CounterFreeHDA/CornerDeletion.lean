import CounterFreeHDA.GluingDeletion

namespace CounterFreeHDA.Corners
universe u
variable {Lab : Type u} {P : PomsetData Lab}

/-- A corner is pure induced deletion when every surviving outside-interface
event is active. The event bijection and both ordered interfaces are derived. -/
noncomputable def asDeletionIso (hP : IsIntervalPom P) (α : Fin P.srcLen → Status)
    (β : Fin P.tgtLen → Status) (hc : Compatible P α β)
    (keep : Fin P.n → Prop) [DecidablePred keep]
    (hk : ∀ e, ¬ Deleted P α β e ↔ keep e)
    (hsrc : ∀ i, keep (P.src i) → α i = Status.star)
    (htgt : ∀ i, keep (P.tgt i) → β i = Status.star) :
    PomsetIso (data P α β hc) (Deletion.data P keep) := by
  classical
  let IP := Induced.index P (fun e => ¬ Deleted P α β e)
  let IQ := Induced.index P keep
  let sub := (Equiv.refl (Fin P.n)).subtypeEquiv (p := fun e => ¬ Deleted P α β e) (q := keep) hk
  let E : Fin (data P α β hc).n ≃ Fin (Deletion.data P keep).n := IP.symm.trans (sub.trans IQ)
  have he : ∀ e, Deletion.inclusion P keep (E e) = inclusion P α β hc e := by
    intro e
    change (IQ.symm (IQ (sub (IP.symm e)))).val = _
    rw [Equiv.symm_apply_apply]
    rfl
  apply PomsetIso.ofEventEquiv (isIntervalPom P α β hP hc) (Deletion.isIntervalPom P keep hP) E
  · intro e; exact congrArg P.lab (he e)
  · intro e f; exact (congrArg₂ P.prec (he e) (he f)).to_iff
  · intro e f; exact (congrArg₂ P.eord (he e) (he f)).to_iff
  · intro e
    have hs : P.inSrc (inclusion P α β hc e) ↔ (data P α β hc).inSrc e := by
      constructor
      · rintro ⟨i,hi⟩
        have hp : keep (P.src i) := hi.symm ▸ ((hk _).mp (inclusion_kept P α β hc e))
        exact (source_iff P α β hc e).mpr ⟨i,hi,hsrc i hp⟩
      · intro h
        obtain ⟨i,hi,_⟩ := (source_iff P α β hc e).mp h
        exact ⟨i,hi⟩
    exact (Deletion.inSrc_iff P keep (E e)).trans ((congrArg P.inSrc (he e)).to_iff.trans hs)
  · intro e
    have hs : P.inTgt (inclusion P α β hc e) ↔ (data P α β hc).inTgt e := by
      constructor
      · rintro ⟨i,hi⟩
        have hp : keep (P.tgt i) := hi.symm ▸ ((hk _).mp (inclusion_kept P α β hc e))
        exact (target_iff P α β hc e).mpr ⟨i,hi,htgt i hp⟩
      · intro h
        obtain ⟨i,hi,_⟩ := (target_iff P α β hc e).mp h
        exact ⟨i,hi⟩
    exact (Deletion.inTgt_iff P keep (E e)).trans ((congrArg P.inTgt (he e)).to_iff.trans hs)

end CounterFreeHDA.Corners
