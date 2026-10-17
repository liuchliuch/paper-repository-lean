import CounterFreeHDA.EndoSurvival
import Mathlib.Data.Fintype.EquivFin

namespace CounterFreeHDA.EndoPom
universe u
variable {Lab : Type u} {U : Interface Lab}

theorem source_label (P : EndoPom U) (i : Fin U.1) :
    P.pom.lab (P.pom.src (Fin.cast P.src_len.symm i)) = U.2 i := by
  obtain ⟨hl,hlabels⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp P.source
  have h := congrFun hlabels (Fin.cast P.src_len.symm i)
  simpa only [Function.comp_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using h

theorem target_label (P : EndoPom U) (i : Fin U.1) :
    P.pom.lab (P.pom.tgt (Fin.cast P.tgt_len.symm i)) = U.2 i := by
  obtain ⟨hl,hlabels⟩ := Fin.sigma_eq_iff_eq_comp_cast.mp P.target
  have h := congrFun hlabels (Fin.cast P.tgt_len.symm i)
  simpa only [Function.comp_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using h

private theorem finite_pow_total {r : ℕ} (f : PartialMap r)
    (total : ∀ i, ∃ j, f i = some j) (n : ℕ) : ∀ i, ∃ j, PartialMap.pow f n i = some j := by
  induction n with
  | zero => intro i; exact ⟨i,rfl⟩
  | succ n ih =>
    intro i
    obtain ⟨j,hj⟩ := ih i
    obtain ⟨l,hl⟩ := total j
    exact ⟨l,by simp only [PartialMap.pow,PartialMap.comp,hj,Option.bind_some,hl]⟩

private noncomputable def sourceEquiv (P : EndoPom U) (hn : P.pom.n = U.1) :
    Fin U.1 ≃ Fin P.pom.n := by
  let f : Fin U.1 → Fin P.pom.n := fun i => P.pom.src (Fin.cast P.src_len.symm i)
  have hf : Function.Injective f := by
    intro i j h
    have hi := P.pom.val.src_inj h
    exact Fin.ext (congrArg (fun x : Fin P.pom.srcLen => x.val) hi)
  exact Equiv.ofBijective f ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hf,by simp only [Fintype.card_fin,hn]⟩)

private theorem all_persistent_of_size_eq (P : EndoPom U) (hn : P.pom.n = U.1) :
    ∀ i : Fin U.1, P.Shared i i := by
  have htgt : Function.Surjective P.pom.val.tgt :=
    ((Fintype.bijective_iff_injective_and_card P.pom.val.tgt).mpr
      ⟨P.pom.val.tgt_inj,by simp only [Fintype.card_fin]; change P.pom.tgtLen = P.pom.n; exact P.tgt_len.trans hn.symm⟩).surjective
  have total : ∀ i, ∃ j, P.survivalU i = some j := by
    intro i
    obtain ⟨j,hj⟩ := htgt (P.pom.src (Fin.cast P.src_len.symm i))
    refine ⟨Fin.cast P.tgt_len j,(survivalU_some_iff P _ _).mpr ?_⟩
    simpa only [Shared,Fin.cast_cast,Fin.cast_refl,id_eq] using hj.symm
  intro i
  have hstable := CounterFreeHDA.lemma_4_1 P.survivalOrder (le_refl U.1) i
  obtain ⟨j,hj⟩ := finite_pow_total P.survivalU total U.1 i
  have hfix : IsFixed P.survivalOrder.toFun i ↔ P.Shared i i := survivalU_some_iff P i i
  by_cases hf : IsFixed P.survivalOrder.toFun i
  · exact hfix.mp hf
  · have hnone : PartialMap.pow P.survivalU U.1 i = none := by
      simpa only [if_neg hf] using hstable
    rw [hj] at hnone
    cases hnone

/-- An endomorphism having no events beyond its interface is isomorphic to
the identity; interface order precludes a permutation of repeated labels. -/
noncomputable def isoIdentityOfSizeEq (P : EndoPom U) (hn : P.pom.n = U.1) :
    PomsetIso P.pom.val (identityPom Lab U.1 U.2).val where
  toEquiv := (sourceEquiv P hn).symm
  lab_eq := by
    intro e
    obtain ⟨i,rfl⟩ := (sourceEquiv P hn).surjective e
    change U.2 ((sourceEquiv P hn).symm ((sourceEquiv P hn) i)) = _
    rw [Equiv.symm_apply_apply]
    exact (P.source_label i).symm
  srcEquiv := finCongr P.src_len
  tgtEquiv := finCongr P.tgt_len
  src_mono := by intro i j; exact Iff.rfl
  tgt_mono := by intro i j; exact Iff.rfl
  src_eq := by
    intro i
    have h := (sourceEquiv P hn).symm_apply_apply (Fin.cast P.src_len i)
    simpa only [sourceEquiv,Equiv.ofBijective_apply,Fin.cast_cast,Fin.cast_refl,id_eq,
      finCongr_apply,identityPom] using h
  tgt_eq := by
    intro j
    have hp := all_persistent_of_size_eq P hn (Fin.cast P.tgt_len j)
    have hs : P.pom.tgt j = (sourceEquiv P hn) (Fin.cast P.tgt_len j) := by
      simpa only [Shared,sourceEquiv,Equiv.ofBijective_apply,Fin.cast_cast,Fin.cast_refl,id_eq] using hp.symm
    change (sourceEquiv P hn).symm (P.pom.tgt j) = Fin.cast P.tgt_len j
    rw [hs,Equiv.symm_apply_apply]
  prec_iff := by
    intro e f
    change False ↔ P.pom.prec e f
    constructor
    · exact False.elim
    · intro hef
      obtain ⟨i,hi⟩ := (sourceEquiv P hn).surjective f
      exact P.pom.property.src_minimal f ⟨Fin.cast P.src_len.symm i,hi⟩ e hef
  eord_iff := by
    intro e f
    obtain ⟨i,rfl⟩ := (sourceEquiv P hn).surjective e
    obtain ⟨j,rfl⟩ := (sourceEquiv P hn).surjective f
    change ((sourceEquiv P hn).symm ((sourceEquiv P hn) i)).val <
      ((sourceEquiv P hn).symm ((sourceEquiv P hn) j)).val ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact (P.pom.property.src_eord (Fin.cast P.src_len.symm i) (Fin.cast P.src_len.symm j)).symm

/-- **Lemma 4.2**, with the original nonidentity hypothesis interpreted up to
pomset isomorphism, and with actual interval-pomset powers. -/
theorem lemma_4_2_full (P : EndoPom U) (hne : ¬ IntervalPomIso P.pom (identityPom Lab U.1 U.2))
    {k n : ℕ} (hk : U.1 ≤ k) (hn : k+1 ≤ n) :
    ∃ e : Fin (P.pow n).pom.n,
      ¬ (P.pow n).pom.val.inSrc e ∧ ¬ (P.pow n).pom.val.inTgt e := by
  have hproper : U.1 < P.pom.n := by
    have hge := P.size_ge
    by_contra h
    have heq : P.pom.n = U.1 := by omega
    exact hne ⟨isoIdentityOfSizeEq P heq⟩
  exact CounterFreeHDA.lemma_4_2_actual P hk hproper hn

end CounterFreeHDA.EndoPom
