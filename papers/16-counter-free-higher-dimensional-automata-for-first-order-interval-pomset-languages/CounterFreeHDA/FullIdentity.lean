import CounterFreeHDA.Width

namespace CounterFreeHDA
universe u
variable {Lab : Type u} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hs : ∀ e, P.inSrc e) (ht : ∀ e, P.inTgt e)

namespace FullIdentity

noncomputable def sourceEquiv : Fin P.srcLen ≃ Fin P.n :=
  Equiv.ofBijective P.src ⟨P.src_inj,hs⟩

include hs ht in
private theorem range_eq : Set.range P.tgt = Set.range P.src := by
  ext e
  exact ⟨fun _ => hs e,fun _ => ht e⟩

noncomputable def targetEquiv : Fin P.tgtLen ≃ Fin P.srcLen :=
  enumerationEquiv P.tgt P.src P.tgt_inj P.src_inj (range_eq P hs ht)

theorem target_event (i : Fin P.tgtLen) :
    P.src (targetEquiv P hs ht i) = P.tgt i := enumerationEquiv_event _ _ _ _ _ i

/-- A pomset whose events all lie in both interfaces is the identity on its
ordered labelled interface, with no hidden permutation of equal labels. -/
noncomputable def iso : PomsetIso P (identityPom Lab P.srcLen (P.lab ∘ P.src)).val where
  toEquiv := (sourceEquiv P hs).symm
  lab_eq e := by
    change P.lab (P.src ((sourceEquiv P hs).symm e)) = P.lab e
    exact congrArg P.lab ((sourceEquiv P hs).apply_symm_apply e)
  srcEquiv := Equiv.refl _
  tgtEquiv := targetEquiv P hs ht
  src_mono _ _ := Iff.rfl
  tgt_mono i j := by
    have hh := congrArg₂ P.eord (target_event P hs ht i) (target_event P hs ht j)
    exact (hP.src_eord _ _).symm.trans (hh.to_iff.trans (hP.tgt_eord i j))
  src_eq i := (sourceEquiv P hs).symm_apply_apply i
  tgt_eq i := by
    change (sourceEquiv P hs).symm (P.tgt i) = targetEquiv P hs ht i
    rw [← target_event P hs ht i]
    exact (sourceEquiv P hs).symm_apply_apply _
  prec_iff e f := iff_of_false not_false (hP.src_minimal f (hs f) e)
  eord_iff e f := by
    change ((sourceEquiv P hs).symm e).val < ((sourceEquiv P hs).symm f).val ↔ P.eord e f
    rw [← hP.src_eord]
    change P.eord ((sourceEquiv P hs) ((sourceEquiv P hs).symm e))
      ((sourceEquiv P hs) ((sourceEquiv P hs).symm f)) ↔ P.eord e f
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]

end FullIdentity
end CounterFreeHDA
