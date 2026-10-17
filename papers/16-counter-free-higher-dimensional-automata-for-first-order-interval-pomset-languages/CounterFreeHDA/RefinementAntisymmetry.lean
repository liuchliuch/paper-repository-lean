import CounterFreeHDA.ActualRecognizer

namespace CounterFreeHDA.IsIntervalPom
universe u
variable {Lab : Type u} {P : PomsetData Lab}

theorem prec_exclusion (hP : IsIntervalPom P) {e f : Fin P.n} (hef : P.prec e f) :
    ¬ P.prec f e ∧ ¬ P.eord e f ∧ ¬ P.eord f e := by
  have hn : e ≠ f := by intro h; subst f; exact hP.prec_irrefl e hef
  exact (hP.trichotomy e f hn).2.1 hef

end CounterFreeHDA.IsIntervalPom

namespace CounterFreeHDA.Refinement
universe u
variable {Lab : Type u} {P Q : IntervalPom Lab}

abbrev PrecPair (P : IntervalPom Lab) := {a : Fin P.n × Fin P.n // P.prec a.1 a.2}

noncomputable def precedenceEmbedding (R : Witness P Q) : PrecPair Q ↪ PrecPair P where
  toFun q := ⟨(R.event.symm q.val.1,R.event.symm q.val.2),R.precedence _ _
    (by simpa only [Equiv.apply_symm_apply] using q.property)⟩
  inj' := by
    intro a b hab
    apply Subtype.ext
    have hh := congrArg Subtype.val hab
    exact Prod.ext (R.event.symm.injective (congrArg Prod.fst hh))
      (R.event.symm.injective (congrArg Prod.snd hh))

/-- On finite event structures, mutual subsumption is actual isomorphism.
Counting precedence pairs turns the inclusion into equality; event order
then follows from exclusivity and the incomparable-pair subsumption law. -/
noncomputable def iso_of_mutual (hpq : P ⊑ₛ Q) (hqp : Q ⊑ₛ P) : PomsetIso P.val Q.val := by
  classical
  let R := witness hpq
  let T := witness hqp
  have hcard : Fintype.card (PrecPair Q) = Fintype.card (PrecPair P) :=
    le_antisymm (Fintype.card_le_of_embedding (precedenceEmbedding R))
      (Fintype.card_le_of_embedding (precedenceEmbedding T))
  have hsurj : Function.Surjective (precedenceEmbedding R) :=
    ((Fintype.bijective_iff_injective_and_card (precedenceEmbedding R)).mpr
      ⟨(precedenceEmbedding R).injective,hcard⟩).surjective
  have hprec : ∀ e f, Q.prec (R.event e) (R.event f) ↔ P.prec e f := by
    intro e f
    refine ⟨R.precedence e f,?_⟩
    intro hef
    obtain ⟨q,hq⟩ := hsurj ⟨(e,f),hef⟩
    have heq := congrArg Subtype.val hq
    have he : q.val.1 = R.event e :=
      (R.event.apply_symm_apply q.val.1).symm.trans (congrArg R.event (congrArg Prod.fst heq))
    have hf : q.val.2 = R.event f :=
      (R.event.apply_symm_apply q.val.2).symm.trans (congrArg R.event (congrArg Prod.snd heq))
    exact (congrArg₂ Q.prec he hf).mp q.property
  exact {
    toEquiv := R.event
    lab_eq e := (R.labels e).symm
    srcEquiv := finCongr R.source_len
    tgtEquiv := finCongr R.target_len
    src_mono _ _ := Iff.rfl
    tgt_mono _ _ := Iff.rfl
    src_eq := R.source
    tgt_eq := R.target
    prec_iff := hprec
    eord_iff e f := by
      by_cases hef : P.prec e f
      · exact iff_of_false (Q.property.prec_exclusion ((hprec e f).mpr hef)).2.1
          (P.property.prec_exclusion hef).2.1
      by_cases hfe : P.prec f e
      · exact iff_of_false (Q.property.prec_exclusion ((hprec f e).mpr hfe)).2.2
          (P.property.prec_exclusion hfe).2.2
      exact (R.order e f hef hfe).symm }

end CounterFreeHDA.Refinement
