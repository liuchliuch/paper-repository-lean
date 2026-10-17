import CounterFreeHDA.CornerIsomorphism

/-! Induced event deletion with both interfaces restricted to all retained
positions. This is the operation P-R used for persistent-event powers. -/
namespace CounterFreeHDA.Deletion
universe u
variable {Lab : Type u} (P : PomsetData Lab) (keep : Fin P.n → Prop) [DecidablePred keep]

noncomputable def source : Finset (Fin P.srcLen) := Finset.univ.filter (fun i => keep (P.src i))
noncomputable def target : Finset (Fin P.tgtLen) := Finset.univ.filter (fun i => keep (P.tgt i))

theorem source_kept {i : Fin P.srcLen} (hi : i ∈ source P keep) : keep (P.src i) := (Finset.mem_filter.mp hi).2
theorem target_kept {i : Fin P.tgtLen} (hi : i ∈ target P keep) : keep (P.tgt i) := (Finset.mem_filter.mp hi).2

noncomputable def data : PomsetData Lab := Induced.data P keep (source P keep) (target P keep)
  (fun _ hi => source_kept P keep hi) (fun _ hi => target_kept P keep hi)

noncomputable def inclusion : Fin (data P keep).n ↪ Fin P.n :=
  Induced.includeEvent P keep (source P keep) (target P keep)
    (fun _ hi => source_kept P keep hi) (fun _ hi => target_kept P keep hi)

noncomputable def retain (e : Fin P.n) (he : keep e) : Fin (data P keep).n := Induced.index P keep ⟨e,he⟩

@[simp] theorem inclusion_retain (e : Fin P.n) (he : keep e) : inclusion P keep (retain P keep e he) = e :=
  congrArg Subtype.val ((Induced.index P keep).symm_apply_apply _)

theorem inclusion_kept (e : Fin (data P keep).n) : keep (inclusion P keep e) :=
  Induced.include_kept P keep _ _ _ _ e

@[simp] theorem retain_inclusion (e : Fin (data P keep).n) :
    retain P keep (inclusion P keep e) (inclusion_kept P keep e) = e := by
  apply (inclusion P keep).injective
  exact inclusion_retain P keep _ _

@[simp] theorem inclusion_source (i : Fin (source P keep).card) :
    inclusion P keep ((data P keep).src i) = P.src ((source P keep).orderEmbOfFin rfl i) :=
  Induced.include_source P keep _ _ _ _ i

@[simp] theorem inclusion_target (i : Fin (target P keep).card) :
    inclusion P keep ((data P keep).tgt i) = P.tgt ((target P keep).orderEmbOfFin rfl i) :=
  Induced.include_target P keep _ _ _ _ i

/-- The new source consists exactly of the retained original source events. -/
theorem inSrc_iff (e : Fin (data P keep).n) : (data P keep).inSrc e ↔ P.inSrc (inclusion P keep e) := by
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨_,(inclusion_source P keep i).symm⟩
  · rintro ⟨i,hi⟩
    have hk : keep (P.src i) := hi.symm ▸ inclusion_kept P keep e
    have hm : i ∈ source P keep := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hk⟩
    let j := (source P keep).orderIsoOfFin rfl |>.symm ⟨i,hm⟩
    have hj : (source P keep).orderEmbOfFin rfl j = i :=
      congrArg Subtype.val ((source P keep).orderIsoOfFin rfl |>.apply_symm_apply ⟨i,hm⟩)
    exact ⟨j,(inclusion P keep).injective ((inclusion_source P keep j).trans ((congrArg P.src hj).trans hi))⟩

/-- The new target consists exactly of the retained original target events. -/
theorem inTgt_iff (e : Fin (data P keep).n) : (data P keep).inTgt e ↔ P.inTgt (inclusion P keep e) := by
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨_,(inclusion_target P keep i).symm⟩
  · rintro ⟨i,hi⟩
    have hk : keep (P.tgt i) := hi.symm ▸ inclusion_kept P keep e
    have hm : i ∈ target P keep := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hk⟩
    let j := (target P keep).orderIsoOfFin rfl |>.symm ⟨i,hm⟩
    have hj : (target P keep).orderEmbOfFin rfl j = i :=
      congrArg Subtype.val ((target P keep).orderIsoOfFin rfl |>.apply_symm_apply ⟨i,hm⟩)
    exact ⟨j,(inclusion P keep).injective ((inclusion_target P keep j).trans ((congrArg P.tgt hj).trans hi))⟩

theorem isIntervalPom (hP : IsIntervalPom P) : IsIntervalPom (data P keep) :=
  Induced.isIntervalPom P keep hP _ _ _ _

theorem widthLE {k : ℕ} (hw : P.WidthLE k) : (data P keep).WidthLE k :=
  hw.ofEmbedding (inclusion P keep) (fun _ _ h => h)

end CounterFreeHDA.Deletion

namespace CounterFreeHDA.PomsetIso
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

/-- Actual induced deletion commutes with event/order/interface isomorphism. -/
noncomputable def deletionIso (φ : PomsetIso P Q) (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)
    (keepP : Fin P.n → Prop) (keepQ : Fin Q.n → Prop) [DecidablePred keepP] [DecidablePred keepQ]
    (hk : ∀ e, keepP e ↔ keepQ (φ.toEquiv e)) :
    PomsetIso (Deletion.data P keepP) (Deletion.data Q keepQ) := by
  let IP := Induced.index P keepP
  let IQ := Induced.index Q keepQ
  let sub := φ.toEquiv.subtypeEquiv hk
  let E : Fin (Deletion.data P keepP).n ≃ Fin (Deletion.data Q keepQ).n := IP.symm.trans (sub.trans IQ)
  have he : ∀ e, Deletion.inclusion Q keepQ (E e) = φ.toEquiv (Deletion.inclusion P keepP e) := by
    intro e
    change (IQ.symm (IQ (sub (IP.symm e)))).val = _
    rw [Equiv.symm_apply_apply]
    rfl
  apply ofEventEquiv (P := Deletion.data P keepP) (Q := Deletion.data Q keepQ)
    (Deletion.isIntervalPom P keepP hP) (Deletion.isIntervalPom Q keepQ hQ) E
  · intro e; exact (congrArg Q.lab (he e)).trans (φ.lab_eq _)
  · intro e f; exact (congrArg₂ Q.prec (he e) (he f)).to_iff.trans (φ.prec_iff _ _)
  · intro e f; exact (congrArg₂ Q.eord (he e) (he f)).to_iff.trans (φ.eord_iff _ _)
  · intro e
    exact (Deletion.inSrc_iff Q keepQ (E e)).trans
      ((congrArg Q.inSrc (he e)).to_iff.trans ((φ.inSrc_image_iff _).trans (Deletion.inSrc_iff P keepP e).symm))
  · intro e
    exact (Deletion.inTgt_iff Q keepQ (E e)).trans
      ((congrArg Q.inTgt (he e)).to_iff.trans ((φ.inTgt_image_iff _).trans (Deletion.inTgt_iff P keepP e).symm))

end CounterFreeHDA.PomsetIso
