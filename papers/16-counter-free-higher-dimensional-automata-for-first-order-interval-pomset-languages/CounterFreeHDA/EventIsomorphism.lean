import CounterFreeHDA.RecognizerFromCategory

namespace CounterFreeHDA.PomsetIso
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

/-- Recover the ordered interface correspondences from an event bijection
that preserves the actual interface event sets. -/
noncomputable def ofEventEquiv (hP : IsIntervalPom P) (hQ : IsIntervalPom Q)
    (e : Fin P.n ≃ Fin Q.n) (hl : ∀ a, Q.lab (e a) = P.lab a)
    (hp : ∀ a b, Q.prec (e a) (e b) ↔ P.prec a b)
    (ho : ∀ a b, Q.eord (e a) (e b) ↔ P.eord a b)
    (hs : ∀ a, Q.inSrc (e a) ↔ P.inSrc a)
    (ht : ∀ a, Q.inTgt (e a) ↔ P.inTgt a) : PomsetIso P Q := by
  have hsrc : Set.range (e ∘ P.src) = Set.range Q.src := by
    ext a
    constructor
    · rintro ⟨i,rfl⟩
      exact (hs (P.src i)).mpr ⟨i,rfl⟩
    · intro ha
      have hqa : Q.inSrc (e (e.symm a)) := by simpa only [Equiv.apply_symm_apply] using ha
      obtain ⟨i,hi⟩ := (hs (e.symm a)).mp hqa
      exact ⟨i,(congrArg e hi).trans (e.apply_symm_apply a)⟩
  have htgt : Set.range (e ∘ P.tgt) = Set.range Q.tgt := by
    ext a
    constructor
    · rintro ⟨i,rfl⟩
      exact (ht (P.tgt i)).mpr ⟨i,rfl⟩
    · intro ha
      have hqa : Q.inTgt (e (e.symm a)) := by simpa only [Equiv.apply_symm_apply] using ha
      obtain ⟨i,hi⟩ := (ht (e.symm a)).mp hqa
      exact ⟨i,(congrArg e hi).trans (e.apply_symm_apply a)⟩
  let s := enumerationEquiv (e ∘ P.src) Q.src (e.injective.comp P.src_inj) Q.src_inj hsrc
  let t := enumerationEquiv (e ∘ P.tgt) Q.tgt (e.injective.comp P.tgt_inj) Q.tgt_inj htgt
  have hs' : ∀ i, Q.src (s i) = e (P.src i) := enumerationEquiv_event _ _ _ _ _
  have ht' : ∀ i, Q.tgt (t i) = e (P.tgt i) := enumerationEquiv_event _ _ _ _ _
  exact {
    toEquiv := e
    lab_eq := hl
    srcEquiv := s
    tgtEquiv := t
    src_mono i j := (hQ.src_eord (s i) (s j)).symm.trans
      ((congrArg₂ Q.eord (hs' i) (hs' j)).to_iff.trans ((ho _ _).trans (hP.src_eord i j)))
    tgt_mono i j := (hQ.tgt_eord (t i) (t j)).symm.trans
      ((congrArg₂ Q.eord (ht' i) (ht' j)).to_iff.trans ((ho _ _).trans (hP.tgt_eord i j)))
    src_eq i := (hs' i).symm
    tgt_eq i := (ht' i).symm
    prec_iff := hp
    eord_iff := ho }

end CounterFreeHDA.PomsetIso
