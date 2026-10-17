import CounterFreeHDA.Reinterface

namespace CounterFreeHDA
universe u v

/-- The unique event-preserving correspondence between two injective
interface enumerations of the same set. -/
noncomputable def enumerationEquiv {E : Type u} {r s : ℕ}
    (a : Fin r → E) (b : Fin s → E) (ha : Function.Injective a)
    (hb : Function.Injective b) (hr : Set.range a = Set.range b) : Fin r ≃ Fin s :=
  (Equiv.ofInjective a ha).trans ((Equiv.setCongr hr).trans (Equiv.ofInjective b hb).symm)

theorem enumerationEquiv_event {E : Type u} {r s : ℕ}
    (a : Fin r → E) (b : Fin s → E) (ha : Function.Injective a)
    (hb : Function.Injective b) (hr : Set.range a = Set.range b) (i : Fin r) :
    b (enumerationEquiv a b ha hb hr i) = a i := by
  unfold enumerationEquiv
  exact Equiv.apply_ofInjective_symm hb _

namespace Reinterface
variable {Lab : Type u} (P : PomsetData Lab) (hP : IsIntervalPom P)

noncomputable def restored : PomsetData Lab :=
  data P hP (sourceSet P) (targetSet P) (source_antichain P hP) (target_antichain P hP)

theorem restored_source : Set.range (restored P hP).src = Set.range P.src := by
  ext e
  exact (inSrc_iff P hP _ _ _ _ e).trans (mem_sourceSet P e)

theorem restored_target : Set.range (restored P hP).tgt = Set.range P.tgt := by
  ext e
  exact (inTgt_iff P hP _ _ _ _ e).trans (mem_targetSet P e)

/-- Re-enumeration of the actual interfaces changes no pomset semantics. -/
noncomputable def restoredIso : PomsetIso (restored P hP) P := by
  let R := restored P hP
  let s := enumerationEquiv R.src P.src R.src_inj P.src_inj (restored_source P hP)
  let t := enumerationEquiv R.tgt P.tgt R.tgt_inj P.tgt_inj (restored_target P hP)
  have hs : ∀ i, P.src (s i) = R.src i := enumerationEquiv_event _ _ _ _ _
  have ht : ∀ i, P.tgt (t i) = R.tgt i := enumerationEquiv_event _ _ _ _ _
  exact {
    toEquiv := Equiv.refl _
    lab_eq _ := rfl
    srcEquiv := s
    tgtEquiv := t
    src_mono i j := by
      rw [← hP.src_eord,hs,hs]
      exact (Antichain.enumeration P hP _ (source_antichain P hP)).ordered i j
    tgt_mono i j := by
      rw [← hP.tgt_eord,ht,ht]
      exact (Antichain.enumeration P hP _ (target_antichain P hP)).ordered i j
    src_eq i := (hs i).symm
    tgt_eq i := (ht i).symm
    prec_iff _ _ := Iff.rfl
    eord_iff _ _ := Iff.rfl }

end Reinterface
end CounterFreeHDA
