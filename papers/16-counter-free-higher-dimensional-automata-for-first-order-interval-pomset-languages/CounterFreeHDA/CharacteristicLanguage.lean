import CounterFreeHDA.RunStop

namespace CounterFreeHDA.PomsetIso
universe u
variable {Lab : Type u}

/-- An actual pomset isomorphism is a subsumption in either direction. -/
theorem subsumption {P Q : IntervalPom Lab} (φ : PomsetIso P.val Q.val) : P ⊑ₛ Q := by
  have hs : P.srcLen = Q.srcLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.srcEquiv
  have ht : P.tgtLen = Q.tgtLen := by simpa only [Fintype.card_fin] using Fintype.card_congr φ.tgtEquiv
  refine ⟨φ.toEquiv,hs,ht,fun e => (φ.lab_eq e).symm,?_,?_,?_,?_⟩
  · intro i
    exact (φ.src_eq i).trans (congrArg Q.src (Fin.ext (φ.srcEquiv_val i)))
  · intro i
    exact (φ.tgt_eq i).trans (congrArg Q.tgt (Fin.ext (φ.tgtEquiv_val i)))
  · intro e f h; exact (φ.prec_iff e f).mp h
  · intro e f _ _; exact (φ.eord_iff e f).symm

end CounterFreeHDA.PomsetIso

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ} {U V : Cube Lab k}

namespace RunLabeling

/-- At the distinguished endpoints every actual event meets the path.
The event injection is therefore a bijection, yielding the required
subsumption with the actual source/target positions. -/
theorem subsumption_complete (A : Arrow U V) (p : Word U V)
    (hr : (track A.pom.val).Run p A.sourceCell A.targetCell) : p.label.pom ⊑ₛ A.pom := by
  classical
  let R := ofRun hr
  have hs : Function.Surjective R.event := by
    intro e
    apply (R.support e).mpr
    constructor
    · change (if A.pom.val.inSrc e then Status.star else Status.zero) ≠ Status.one
      split_ifs <;> decide
    · change (if A.pom.val.inTgt e then Status.star else Status.one) ≠ Status.zero
      split_ifs <;> decide
  let E := Equiv.ofBijective R.event ⟨R.event.injective,hs⟩
  let hsrc := p.label.src_len.trans A.src_len.symm
  let htgt := p.label.tgt_len.trans A.tgt_len.symm
  refine ⟨E,hsrc,htgt,fun e => (R.labels e).symm,?_,?_,R.precedence,R.order⟩
  · intro i
    exact (R.source i).trans (congrArg A.pom.src (Fin.ext rfl))
  · intro i
    exact (R.target i).trans (congrArg A.pom.tgt (Fin.ext rfl))

end RunLabeling

namespace Arrow

/-- **Lemma 3.1(a).** The complete labels of the actual characteristic HDA
are exactly the subsumptions of its defining pomset. -/
theorem lemma_3_1_a (A B : Arrow U V) (hw : A.pom.val.WidthLE k) :
    B.targetCell ∈ (track B.pom.val).dPom B.sourceCell A.pom ↔ A.pom ⊑ₛ B.pom := by
  constructor
  · rintro ⟨p,hr,⟨φ⟩⟩
    exact subsumption_trans φ.symm.subsumption (RunLabeling.subsumption_complete B p hr)
  · intro h
    exact Refinement.complete_path A B h hw

end Arrow

namespace HDA

/-- Every actual HDA language is downward closed on the bounded-width
interval-pomset source, including nonempty initial and final interfaces. -/
theorem language_downward (X : HDA.{u,v} Lab k) {P Q : IntervalPom Lab}
    (hw : P.val.WidthLE k) (h : P ⊑ₛ Q) (hQ : Q ∈ X.LangPom) : P ∈ X.LangPom := by
  classical
  obtain ⟨U,V,x,y,hx,hy,p,hr,⟨φ⟩⟩ := hQ
  let B : Arrow U V := {
    pom := Q
    source := φ.source_type.symm.trans p.label.source
    target := φ.target_type.symm.trans p.label.target }
  let R := Refinement.witness h
  let A : Arrow U V := {
    pom := P
    source := R.source_type.trans B.source
    target := R.target_type.trans B.target }
  refine ⟨U,V,x,y,hx,hy,?_⟩
  exact Refinement.reachability_downward A B x y h hw ⟨p,hr,⟨φ⟩⟩

end HDA
end CounterFreeHDA.Cubical
