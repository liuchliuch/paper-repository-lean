import CounterFreeHDA.RunStart

namespace CounterFreeHDA.Cubical.RunLabeling.Stop
universe u
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab} {U V W : Cube Lab k}
variable (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1)
    (p : Word V W) (x : TrackCell P U) (y : TrackCell P W)
    (R : RunLabeling p (x.face f) y)

abbrev step : Step U V := .stop f hu hd
noncomputable abbrev leftArrow := (step f hu hd).label
noncomputable abbrev rightArrow := p.label

noncomputable def matching : GlueMatch (leftArrow f hu hd).pom.val p.label.pom.val :=
  GlueMatch.ofType ((leftArrow f hu hd).target.trans p.label.source.symm)

noncomputable def atlas : GluingEmbedding (matching f hu hd p) P := by
  classical
  let A := leftArrow f hu hd
  let B := p.label
  let m := matching f hu hd p
  have hseam : ∀ i : Fin V.dim,
      R.event (B.pom.src (Fin.cast B.src_len.symm i)) = x.occ (f.position i) := by
    intro i
    exact (R.source _).trans (congrArg (fun j => x.occ (f.position j)) (Fin.ext rfl))
  exact {
    left := ⟨x.occ,x.inj⟩
    right := R.event
    seam i := by
      change x.occ (f.position i) = R.event (B.pom.src (Fin.cast m.len_eq i))
      exact (hseam i).symm
    overlap a b hab := by
      have hs := ((R.support _).mp ⟨b,rfl⟩).1
      have hf := TrackCell.face_status_occ f x a
      change (x.face f).status (x.occ a) = f.status a at hf
      have hna : f.status a ≠ Status.one := by
        intro h
        apply hs
        exact (congrArg (x.face f).status hab.symm).trans (hf.trans h)
      cases hsub : f.sub a with
      | inr c =>
        have hc := hu a c hsub
        subst c
        exact False.elim (hna (by simp only [Face.status,hsub]))
      | inl i =>
        have hpos : f.position i = a := (f.position_unique hsub).symm
        refine ⟨i,hpos,R.event.injective ?_⟩
        change R.event (B.pom.src (Fin.cast m.len_eq i)) = R.event b
        exact (hseam i).trans ((congrArg x.occ hpos).trans hab) }

/-- The seam has the same actual event at either occurrence. -/
theorem seam_event (i : Fin V.dim) :
    x.occ (f.position i) = R.event (p.label.pom.src (Fin.cast (matching f hu hd p).len_eq i)) :=
  (atlas f hu hd p x y R).seam i

theorem raw_labels (a : GluedE (leftArrow f hu hd).pom.val p.label.pom.val) :
    P.lab ((atlas f hu hd p x y R).raw a) = glueLab (matching f hu hd p) a := by
  cases a with
  | left a => exact x.labels a.val
  | right a => exact R.labels a.val
  | mid i => exact x.labels (f.position i)

private theorem active_no_prec (a b : Fin U.dim) : ¬ P.prec (x.occ a) (x.occ b) := by
  intro hab
  have hb : x.status (x.occ b) ≠ Status.zero := by rw [x.active]; decide
  have hh := x.config _ _ hab hb
  have hv : x.status (x.occ a) = Status.one := hh
  rw [x.active] at hv
  exact (by decide : Status.star ≠ Status.one) hv

include hu hd in
/-- An event of the residual label outside its source is still unstarted
before this termination, so it cannot precede a currently active event. -/
private theorem future_no_prec (b : Fin p.label.pom.n) (hb : ¬ p.label.pom.val.inSrc b)
    (a : Fin U.dim) : ¬ P.prec (R.event b) (x.occ a) := by
  have hz := R.source_zero b hb
  have hs := TrackCell.le_upper_status f hu x (R.event b)
  rw [hz] at hs
  have hzero : x.status (R.event b) = Status.zero := by
    apply Fin.ext
    change (x.status (R.event b)).val = 0
    change (x.status (R.event b)).val ≤ 0 at hs
    omega
  intro hab
  have ha : x.status (x.occ a) ≠ Status.zero := by rw [x.active]; decide
  have hh := x.config _ _ hab ha
  have hv : x.status (R.event b) = Status.one := hh
  rw [hzero] at hv
  exact (by decide : Status.zero ≠ Status.one) hv

/-- Every ambient precedence forced by configuration (8) also holds in the
actual glued step/tail label. -/
theorem raw_precedence (a b : GluedE (leftArrow f hu hd).pom.val p.label.pom.val)
    (hab : P.prec ((atlas f hu hd p x y R).raw a) ((atlas f hu hd p x y R).raw b)) :
    gluePrec (matching f hu hd p).len_eq a b := by
  cases a with
  | left a =>
    cases b with
    | left b => exact False.elim (active_no_prec x a.val b.val hab)
    | right b => trivial
    | mid i => exact False.elim (active_no_prec x a.val (f.position i) hab)
  | right a =>
    cases b with
    | left b => exact False.elim (future_no_prec f hu hd p x y R a.val a.property b.val hab)
    | right b => exact R.precedence _ _ hab
    | mid i =>
      change P.prec (R.event a.val) (x.occ (f.position i)) at hab
      have hh : P.prec (R.event a.val) (R.event (p.label.pom.src (Fin.cast (matching f hu hd p).len_eq i))) :=
        (congrArg (P.prec (R.event a.val)) (seam_event f hu hd p x y R i)).mp hab
      exact False.elim (p.label.pom.property.src_minimal _ ⟨_,rfl⟩ _ (R.precedence _ _ hh))
  | mid i =>
    cases b with
    | left b => exact False.elim (active_no_prec x (f.position i) b.val hab)
    | right b =>
      change P.prec (x.occ (f.position i)) (R.event b.val) at hab
      have hh : P.prec (R.event (p.label.pom.src (Fin.cast (matching f hu hd p).len_eq i))) (R.event b.val) :=
        (congrArg (fun e => P.prec e (R.event b.val)) (seam_event f hu hd p x y R i)).mp hab
      exact R.precedence _ _ hh
    | mid j => exact False.elim (active_no_prec x (f.position i) (f.position j) hab)

/-- Event order agrees on pairs still incomparable in the actual path label. -/
theorem raw_order (a b : GluedE (leftArrow f hu hd).pom.val p.label.pom.val)
    (hab : ¬ gluePrec (matching f hu hd p).len_eq a b)
    (hba : ¬ gluePrec (matching f hu hd p).len_eq b a) :
    glueEord (matching f hu hd p).len_eq a b ↔
      P.eord ((atlas f hu hd p x y R).raw a) ((atlas f hu hd p x y R).raw b) := by
  cases a with
  | left a =>
    cases b with
    | left b => exact (x.ordered a.val b.val).symm
    | right b => exact False.elim (hab trivial)
    | mid i => exact (x.ordered a.val (f.position i)).symm
  | right a =>
    cases b with
    | left b => exact False.elim (hba trivial)
    | right b => exact R.order a.val b.val hab hba
    | mid i =>
      have hsrc := p.label.pom.property.src_minimal
        (p.label.pom.src (Fin.cast (matching f hu hd p).len_eq i)) ⟨_,rfl⟩ a.val
      have hh := R.order a.val (p.label.pom.src (Fin.cast (matching f hu hd p).len_eq i)) hsrc hba
      exact hh.trans (congrArg (P.eord (R.event a.val)) (seam_event f hu hd p x y R i).symm).to_iff
  | mid i =>
    cases b with
    | left b => exact (x.ordered (f.position i) b.val).symm
    | right b =>
      have hsrc := p.label.pom.property.src_minimal
        (p.label.pom.src (Fin.cast (matching f hu hd p).len_eq i)) ⟨_,rfl⟩ b.val
      have hh := R.order (p.label.pom.src (Fin.cast (matching f hu hd p).len_eq i)) b.val hab hsrc
      exact hh.trans (congrArg (fun e => P.eord e (R.event b.val)) (seam_event f hu hd p x y R i).symm).to_iff
    | mid j => exact (x.ordered (f.position i) (f.position j)).symm

end CounterFreeHDA.Cubical.RunLabeling.Stop
