import CounterFreeHDA.UnaryWordExpression

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

private theorem closed_word_size (p : ClosedWord) : p.length = 2*p.label.pom.n := by
  have h := p.stMeasure_label
  have hs := p.label.src_len
  have ht := p.label.tgt_len
  change p.label.pom.srcLen = 0 at hs
  change p.label.pom.tgtLen = 0 at ht
  change 2*p.label.pom.n-p.label.pom.srcLen-p.label.pom.tgtLen = p.length at h
  rw [hs,ht] at h
  omega

theorem single_block_size {p : ClosedWord} (h : SingleBlock p) : p.label.pom.n = 1 := by
  have hl : p.length = 2 := by cases h; rfl
  have hn := closed_word_size p
  omega

theorem concurrent_block_size {p : ClosedWord} (h : ConcurrentBlock p) : p.label.pom.n = 2 := by
  have hl : p.length = 4 := by cases h; rfl
  have hn := closed_word_size p
  omega

theorem concurrent_block_prec {p : ClosedWord} (hc : ConcurrentBlock p) :
    ∀ e f, ¬ p.label.pom.prec e f := by
  have hn := concurrent_block_size hc
  cases hc with
  | @mk U V W f g h l hf hg hh hl hU hV hW h0 =>
    let p : ClosedWord := .cons (.start f hf hU) (.cons (.start g hg hV)
      (.cons (.stop h hh hW) (.cons (.stop l hl h0) (.nil _))))
    have hr := p.canonicalRun
    obtain ⟨z,hz,hrest⟩ := ((track p.label.pom.val).run_start_iff f hf hU _ _ _).mp hr
    obtain ⟨q,hq,hrest'⟩ := ((track p.label.pom.val).run_start_iff g hg hV _ _ _).mp hrest
    change p.label.pom.n = 2 at hn
    have hdim : V.dim = p.label.pom.n := by
      have hU' : U.dim = 1 := hU
      have hV' : V.dim = U.dim+1 := hV
      omega
    have hsur : Function.Surjective q.occ :=
      ((Fintype.bijective_iff_injective_and_card q.occ).mpr
        ⟨q.inj,by simp only [Fintype.card_fin]; exact hdim⟩).surjective
    intro e f hef
    obtain ⟨i,rfl⟩ := hsur e
    obtain ⟨j,rfl⟩ := hsur f
    have hterm := q.config _ _ hef (by rw [q.active j]; decide)
    have hbad := (q.active i).symm.trans hterm
    exact (by decide : Status.star ≠ Status.one) hbad

/-- All closed discrete unary pomsets with a fixed number of events are
isomorphic with both orders and interfaces, by ordered antichain enumeration. -/
noncomputable def closedDiscreteIso (P Q : Tail Completion.emptyCube)
    (hn : P.pom.n = Q.pom.n)
    (hp : ∀ e f, ¬ P.pom.prec e f) (hq : ∀ e f, ¬ Q.pom.prec e f) : PomsetIso P.pom.val Q.pom.val := by
  classical
  let ep := Antichain.enumeration P.pom.val P.pom.property Finset.univ (fun e _ f _ => hp e f)
  let eq := Antichain.enumeration Q.pom.val Q.pom.property Finset.univ (fun e _ f _ => hq e f)
  have cp : (Finset.univ : Finset (Fin P.pom.n)).card = P.pom.n := by simp
  have cq : (Finset.univ : Finset (Fin Q.pom.n)).card = Q.pom.n := by simp
  let ap : Fin P.pom.n → Fin P.pom.n := fun i => ep.event (Fin.cast cp.symm i)
  let aq : Fin Q.pom.n → Fin Q.pom.n := fun i => eq.event (Fin.cast cq.symm i)
  have hap : Function.Bijective ap := (Fintype.bijective_iff_injective_and_card ap).mpr
    ⟨fun _ _ h => Fin.ext (congrArg (fun i : Fin Finset.univ.card => i.val) (ep.injective h)),rfl⟩
  have haq : Function.Bijective aq := (Fintype.bijective_iff_injective_and_card aq).mpr
    ⟨fun _ _ h => Fin.ext (congrArg (fun i : Fin Finset.univ.card => i.val) (eq.injective h)),rfl⟩
  let EP := Equiv.ofBijective ap hap
  let EQ := Equiv.ofBijective aq haq
  let E := EP.symm.trans ((finCongr hn).trans EQ)
  apply PomsetIso.ofEventEquiv P.pom.property Q.pom.property E
  · intro e; exact Subsingleton.elim _ _
  · intro e f; exact iff_of_false (hq _ _) (hp _ _)
  · intro e f
    obtain ⟨i,rfl⟩ := EP.surjective e
    obtain ⟨j,rfl⟩ := EP.surjective f
    change Q.pom.eord (EQ (Fin.cast hn (EP.symm (EP i)))) (EQ (Fin.cast hn (EP.symm (EP j)))) ↔ _
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    exact (eq.ordered _ _).trans
      ((show Fin.cast cq.symm (Fin.cast hn i) < Fin.cast cq.symm (Fin.cast hn j) ↔
          Fin.cast cp.symm i < Fin.cast cp.symm j from Iff.rfl).trans (ep.ordered _ _).symm)
  · intro e
    exact iff_of_false (by rintro ⟨i,_⟩; exact Fin.elim0 (Fin.cast Q.toArrow.src_len i))
      (by rintro ⟨i,_⟩; exact Fin.elim0 (Fin.cast P.toArrow.src_len i))
  · intro e
    exact iff_of_false (by rintro ⟨i,_⟩; exact Fin.elim0 (Fin.cast Q.toArrow.tgt_len i))
      (by rintro ⟨i,_⟩; exact Fin.elim0 (Fin.cast P.toArrow.tgt_len i))

def cWord : ClosedWord := Unary.H.append Unary.end2

theorem cWord_concurrent : ConcurrentBlock cWord :=
  .mk _ _ _ _ Completion.lowerFace Unary.face1_lower Unary.face1_upper Completion.upperFace rfl rfl rfl rfl

noncomputable def cPom : EndoPom (cubeInterface Completion.emptyCube) where
  pom := cWord.label.pom
  source := cWord.label.source
  target := cWord.label.target

noncomputable def aPom : EndoPom (cubeInterface Completion.emptyCube) where
  pom := Unary.a.label.pom
  source := Unary.a.label.source
  target := Unary.a.label.target

theorem aWord_single : SingleBlock Unary.a := .mk _ _ Completion.lowerFace Completion.upperFace rfl

noncomputable def singleBlockIso {p : ClosedWord} (hp : SingleBlock p) : PomsetIso p.label.pom.val aPom.pom.val := by
  have hn := single_block_size hp
  have hna := single_block_size aWord_single
  have hp' : ∀ e f, ¬ p.label.pom.prec e f := by
    intro e f hef
    have he : e = f := Fin.ext (by have he := e.isLt; have hf := f.isLt; omega)
    exact p.label.pom.property.prec_irrefl _ (he ▸ hef)
  have ha' : ∀ e f, ¬ aPom.pom.prec e f := by
    intro e f hef
    have he : e = f := Fin.ext (by have he := e.isLt; have hf := f.isLt; change e.val < Unary.a.label.pom.n at he; change f.val < Unary.a.label.pom.n at hf; omega)
    exact aPom.pom.property.prec_irrefl _ (he ▸ hef)
  exact closedDiscreteIso (BoundedArrow.ofWord p) (BoundedArrow.ofWord Unary.a) (hn.trans hna.symm) hp' ha'

noncomputable def concurrentBlockIso {p : ClosedWord} (hp : ConcurrentBlock p) : PomsetIso p.label.pom.val cPom.pom.val :=
  closedDiscreteIso (BoundedArrow.ofWord p) (BoundedArrow.ofWord cWord)
    ((concurrent_block_size hp).trans (concurrent_block_size cWord_concurrent).symm)
    (concurrent_block_prec hp) (concurrent_block_prec cWord_concurrent)

end CounterFreeHDA.Appendix.Residual
