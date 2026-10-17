import CounterFreeHDA.CornerBoundary

namespace CounterFreeHDA.Cubical.RunLabeling
universe u
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab} {U V : Cube Lab k}

/-- Restrict the actual event occurrences of a path to any induced pomset
whose event image and ordered endpoints match the lifetime support. -/
theorem restrict_subsumption (A : Arrow U V) (p : Word U V)
    {x : TrackCell P U} {y : TrackCell P V} (R : RunLabeling p x y)
    (ι : Fin A.pom.n ↪ Fin P.n)
    (hl : ∀ e, P.lab (ι e) = A.pom.lab e)
    (hp : ∀ e f, P.prec (ι e) (ι f) ↔ A.pom.prec e f)
    (ho : ∀ e f, P.eord (ι e) (ι f) ↔ A.pom.eord e f)
    (hsupport : ∀ e, (∃ a, ι a = e) ↔ x.status e ≠ Status.one ∧ y.status e ≠ Status.zero)
    (hsrc : ∀ i : Fin U.dim, ι (A.pom.src (Fin.cast A.src_len.symm i)) = x.occ i)
    (htgt : ∀ i : Fin V.dim, ι (A.pom.tgt (Fin.cast A.tgt_len.symm i)) = y.occ i) :
    p.label.pom ⊑ₛ A.pom := by
  classical
  have hr : Set.range R.event = Set.range ι := by
    ext e
    exact (R.support e).trans (hsupport e).symm
  let E := enumerationEquiv R.event ι R.event.injective ι.injective hr
  have he : ∀ e, ι (E e) = R.event e := enumerationEquiv_event _ _ _ _ _
  let hsource := p.label.src_len.trans A.src_len.symm
  let htarget := p.label.tgt_len.trans A.tgt_len.symm
  refine ⟨E,hsource,htarget,?_,?_,?_,?_,?_⟩
  · intro e
    exact (R.labels e).symm.trans ((congrArg P.lab (he e)).symm.trans (hl (E e)))
  · intro i
    apply ι.injective
    exact (he _).trans ((R.source i).trans ((hsrc (Fin.cast p.label.src_len i)).symm.trans
      (congrArg (fun j => ι (A.pom.src j)) (Fin.ext rfl))))
  · intro i
    apply ι.injective
    exact (he _).trans ((R.target i).trans ((htgt (Fin.cast p.label.tgt_len i)).symm.trans
      (congrArg (fun j => ι (A.pom.tgt j)) (Fin.ext rfl))))
  · intro e f hef
    apply R.precedence
    exact (congrArg₂ P.prec (he e) (he f)).mp ((hp _ _).mpr hef)
  · intro e f hef hfe
    exact (R.order e f hef hfe).trans
      (((congrArg₂ P.eord (he e) (he f)).to_iff.symm).trans (ho _ _))

end CounterFreeHDA.Cubical.RunLabeling
