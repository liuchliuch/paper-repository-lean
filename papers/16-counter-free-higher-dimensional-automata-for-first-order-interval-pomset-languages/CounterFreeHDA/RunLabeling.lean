import CounterFreeHDA.RefinementPaths
import CounterFreeHDA.GluingEmbedding

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab}

/-- The actual event occurrences of a labelled characteristic path. The
image consists precisely of events whose lifetime meets the recorded path. -/
structure RunLabeling {U V : Cube Lab k} (p : Word U V)
    (x : TrackCell P U) (y : TrackCell P V) where
  event : Fin p.label.pom.n ↪ Fin P.n
  labels : ∀ e, P.lab (event e) = p.label.pom.lab e
  source : ∀ i, event (p.label.pom.src i) = x.occ (Fin.cast p.label.src_len i)
  target : ∀ i, event (p.label.pom.tgt i) = y.occ (Fin.cast p.label.tgt_len i)
  support : ∀ e, (∃ a, event a = e) ↔ x.status e ≠ Status.one ∧ y.status e ≠ Status.zero
  precedence : ∀ e f, P.prec (event e) (event f) → p.label.pom.prec e f
  order : ∀ e f, ¬ p.label.pom.prec e f → ¬ p.label.pom.prec f e →
    (p.label.pom.eord e f ↔ P.eord (event e) (event f))

namespace RunLabeling
variable {U V : Cube Lab k} {p : Word U V} {x : TrackCell P U} {y : TrackCell P V}
    (R : RunLabeling p x y)

theorem source_active (a : Fin p.label.pom.n) :
    x.status (R.event a) = Status.star ↔ p.label.pom.val.inSrc a := by
  constructor
  · intro ha
    obtain ⟨i,hi⟩ := x.covers _ ha
    refine ⟨Fin.cast p.label.src_len.symm i,R.event.injective ?_⟩
    exact (R.source _).trans (by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hi)
  · rintro ⟨i,rfl⟩
    exact (congrArg x.status (R.source i)).trans (x.active _)

theorem target_active (a : Fin p.label.pom.n) :
    y.status (R.event a) = Status.star ↔ p.label.pom.val.inTgt a := by
  constructor
  · intro ha
    obtain ⟨i,hi⟩ := y.covers _ ha
    refine ⟨Fin.cast p.label.tgt_len.symm i,R.event.injective ?_⟩
    exact (R.target _).trans (by simpa only [Fin.cast_cast,Fin.cast_refl,id_eq] using hi)
  · rintro ⟨i,rfl⟩
    exact (congrArg y.status (R.target i)).trans (y.active _)

theorem source_zero (a : Fin p.label.pom.n) (ha : ¬ p.label.pom.val.inSrc a) :
    x.status (R.event a) = Status.zero := by
  have hn := ((R.support _).mp ⟨a,rfl⟩).1
  have hs : x.status (R.event a) ≠ Status.star := fun h => ha ((R.source_active a).mp h)
  have hv := (x.status (R.event a)).isLt
  apply Fin.ext
  change (x.status (R.event a)).val = 0
  have hne1 : (x.status (R.event a)).val ≠ 1 := fun h => hs (Fin.ext h)
  have hne2 : (x.status (R.event a)).val ≠ 2 := fun h => hn (Fin.ext h)
  omega

theorem target_one (a : Fin p.label.pom.n) (ha : ¬ p.label.pom.val.inTgt a) :
    y.status (R.event a) = Status.one := by
  have hn := ((R.support _).mp ⟨a,rfl⟩).2
  have hs : y.status (R.event a) ≠ Status.star := fun h => ha ((R.target_active a).mp h)
  have hv := (y.status (R.event a)).isLt
  apply Fin.ext
  change (y.status (R.event a)).val = 2
  have hne1 : (y.status (R.event a)).val ≠ 1 := fun h => hs (Fin.ext h)
  have hne0 : (y.status (R.event a)).val ≠ 0 := fun h => hn (Fin.ext h)
  omega

noncomputable def nil (c : TrackCell P U) : RunLabeling (.nil U) c c where
  event := ⟨c.occ,c.inj⟩
  labels := c.labels
  source _ := rfl
  target _ := rfl
  support e := by
    constructor
    · rintro ⟨i,rfl⟩
      change c.status (c.occ i) ≠ Status.one ∧ c.status (c.occ i) ≠ Status.zero
      rw [c.active]
      decide
    · rintro ⟨h1,h0⟩
      apply c.covers
      have hv := (c.status e).isLt
      have hn1 : (c.status e).val ≠ 2 := fun h => h1 (Fin.ext h)
      have hn0 : (c.status e).val ≠ 0 := fun h => h0 (Fin.ext h)
      apply Fin.ext
      change (c.status e).val = 1
      omega
  precedence e f hef := by
    have hn : c.status (c.occ f) ≠ Status.zero := by rw [c.active]; decide
    have hh : c.status (c.occ e) = Status.one := c.config _ _ hef hn
    rw [c.active] at hh
    exact False.elim ((by decide : Status.star ≠ Status.one) hh)
  order e f _ _ := (c.ordered e f).symm

end RunLabeling
end CounterFreeHDA.Cubical
