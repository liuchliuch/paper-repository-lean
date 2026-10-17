import CounterFreeHDA.Reachability

namespace CounterFreeHDA.PomsetIso
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

/-- Transport actual face-status assignments along the ordered interfaces. -/
theorem corner_compatible (φ : PomsetIso P Q) (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status)
    (hc : Corners.Compatible P α β) :
    Corners.Compatible Q (α ∘ φ.srcEquiv.symm) (β ∘ φ.tgtEquiv.symm) := by
  intro i j hij
  apply hc
  apply φ.toEquiv.injective
  exact (φ.src_eq _).trans ((congrArg Q.src (φ.srcEquiv.apply_symm_apply i)).trans
    (hij.trans ((congrArg Q.tgt (φ.tgtEquiv.apply_symm_apply j)).symm.trans (φ.tgt_eq _).symm)))

theorem corner_deleted (φ : PomsetIso P Q) (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status)
    (e : Fin P.n) :
    Corners.Deleted Q (α ∘ φ.srcEquiv.symm) (β ∘ φ.tgtEquiv.symm) (φ.toEquiv e) ↔
      Corners.Deleted P α β e := by
  constructor
  · rintro (⟨i,hi,hα⟩ | ⟨j,hj,hβ⟩)
    · refine Or.inl ⟨φ.srcEquiv.symm i,φ.toEquiv.injective ?_,hα⟩
      exact (φ.src_eq _).trans ((congrArg Q.src (φ.srcEquiv.apply_symm_apply i)).trans hi)
    · refine Or.inr ⟨φ.tgtEquiv.symm j,φ.toEquiv.injective ?_,hβ⟩
      exact (φ.tgt_eq _).trans ((congrArg Q.tgt (φ.tgtEquiv.apply_symm_apply j)).trans hj)
  · rintro (⟨i,hi,hα⟩ | ⟨j,hj,hβ⟩)
    · exact Or.inl ⟨φ.srcEquiv i,(φ.src_eq i).symm.trans (congrArg φ.toEquiv hi),
        by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hα⟩
    · exact Or.inr ⟨φ.tgtEquiv j,(φ.tgt_eq j).symm.trans (congrArg φ.toEquiv hj),
        by simpa only [Function.comp_apply,Equiv.symm_apply_apply] using hβ⟩

/-- The actual corner construction preserves pomset isomorphisms, including
all deleted events, induced orders and newly active ordered interfaces. -/
noncomputable def cornerIso (φ : PomsetIso P Q) (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)
    (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status) (hc : Corners.Compatible P α β) :
    PomsetIso (Corners.data P α β hc)
      (Corners.data Q (α ∘ φ.srcEquiv.symm) (β ∘ φ.tgtEquiv.symm) (φ.corner_compatible α β hc)) := by
  classical
  let aQ := α ∘ φ.srcEquiv.symm
  let bQ := β ∘ φ.tgtEquiv.symm
  let hcQ := φ.corner_compatible α β hc
  let IP := Induced.index P (fun e => ¬ Corners.Deleted P α β e)
  let IQ := Induced.index Q (fun e => ¬ Corners.Deleted Q aQ bQ e)
  let sub := φ.toEquiv.subtypeEquiv (p := fun e => ¬ Corners.Deleted P α β e)
    (q := fun e => ¬ Corners.Deleted Q aQ bQ e) (fun e => (φ.corner_deleted α β e).not.symm)
  let E := IP.symm.trans (sub.trans IQ)
  have he : ∀ e, Corners.inclusion Q aQ bQ hcQ (E e) = φ.toEquiv (Corners.inclusion P α β hc e) := by
    intro e
    change (IQ.symm (IQ (sub (IP.symm e)))).val = _
    rw [Equiv.symm_apply_apply]
    rfl
  apply ofEventEquiv (Corners.isIntervalPom P α β hP hc) (Corners.isIntervalPom Q aQ bQ hQ hcQ) E
  · intro e
    exact (congrArg Q.lab (he e)).trans (φ.lab_eq _)
  · intro e f
    exact (congrArg₂ Q.prec (he e) (he f)).to_iff.trans (φ.prec_iff _ _)
  · intro e f
    exact (congrArg₂ Q.eord (he e) (he f)).to_iff.trans (φ.eord_iff _ _)
  · intro e
    apply (Corners.source_iff Q aQ bQ hcQ (E e)).trans
    apply Iff.trans ?_ (Corners.source_iff P α β hc e).symm
    constructor
    · rintro ⟨i,hi,hα⟩
      refine ⟨φ.srcEquiv.symm i,φ.toEquiv.injective ?_,hα⟩
      exact (φ.src_eq _).trans ((congrArg Q.src (φ.srcEquiv.apply_symm_apply i)).trans (hi.trans (he e)))
    · rintro ⟨i,hi,hα⟩
      refine ⟨φ.srcEquiv i,(φ.src_eq i).symm.trans ((congrArg φ.toEquiv hi).trans (he e).symm),?_⟩
      simpa only [aQ,Function.comp_apply,Equiv.symm_apply_apply] using hα
  · intro e
    apply (Corners.target_iff Q aQ bQ hcQ (E e)).trans
    apply Iff.trans ?_ (Corners.target_iff P α β hc e).symm
    constructor
    · rintro ⟨i,hi,hβ⟩
      refine ⟨φ.tgtEquiv.symm i,φ.toEquiv.injective ?_,hβ⟩
      exact (φ.tgt_eq _).trans ((congrArg Q.tgt (φ.tgtEquiv.apply_symm_apply i)).trans (hi.trans (he e)))
    · rintro ⟨i,hi,hβ⟩
      refine ⟨φ.tgtEquiv i,(φ.tgt_eq i).symm.trans ((congrArg φ.toEquiv hi).trans (he e).symm),?_⟩
      simpa only [bQ,Function.comp_apply,Equiv.symm_apply_apply] using hβ

end CounterFreeHDA.PomsetIso
