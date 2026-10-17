import CounterFreeHDA.WordTrack

namespace CounterFreeHDA
universe u
variable {Lab : Type u} {P Q : PomsetData Lab}

namespace PomsetIso

theorem inSrc_image_iff (φ : PomsetIso P Q) (e : Fin P.n) : Q.inSrc (φ.toEquiv e) ↔ P.inSrc e := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨φ.srcEquiv.symm j,φ.toEquiv.injective ?_⟩
    exact (φ.src_eq _).trans (by simpa only [Equiv.apply_symm_apply] using hj)
  · rintro ⟨i,hi⟩
    exact ⟨φ.srcEquiv i,(φ.src_eq i).symm.trans (congrArg φ.toEquiv hi)⟩

theorem inTgt_image_iff (φ : PomsetIso P Q) (e : Fin P.n) : Q.inTgt (φ.toEquiv e) ↔ P.inTgt e := by
  constructor
  · rintro ⟨j,hj⟩
    refine ⟨φ.tgtEquiv.symm j,φ.toEquiv.injective ?_⟩
    exact (φ.tgt_eq _).trans (by simpa only [Equiv.apply_symm_apply] using hj)
  · rintro ⟨i,hi⟩
    exact ⟨φ.tgtEquiv i,(φ.tgt_eq i).symm.trans (congrArg φ.toEquiv hi)⟩

end PomsetIso
end CounterFreeHDA

namespace CounterFreeHDA.Cubical
universe u v w z
variable {Lab : Type u} {k : ℕ} {P Q : PomsetData Lab}

namespace Map

def comp {X : Precubical.{u,v} Lab k} {Y : Precubical.{u,w} Lab k}
    {Z : Precubical.{u,z} Lab k} (a : Map X Y) (b : Map Y Z) : Map X Z where
  app c := b.app (a.app c)
  natural f c := (congrArg b.app (a.natural f c)).trans (b.natural f (a.app c))

end Map

namespace TrackIso

/-- Reindex a characteristic cell by the actual event isomorphism. -/
def transport (φ : PomsetIso P Q) {U : Cube Lab k} (c : TrackCell P U) : TrackCell Q U where
  status e := c.status (φ.toEquiv.symm e)
  config e f hef hf := by
    have hp : P.prec (φ.toEquiv.symm e) (φ.toEquiv.symm f) :=
      (φ.prec_iff _ _).mp (by simpa only [Equiv.apply_symm_apply] using hef)
    exact c.config _ _ hp hf
  occ i := φ.toEquiv (c.occ i)
  inj := φ.toEquiv.injective.comp c.inj
  active i := by simpa only [Equiv.symm_apply_apply] using c.active i
  covers e he := by
    obtain ⟨i,hi⟩ := c.covers (φ.toEquiv.symm e) he
    exact ⟨i,(congrArg φ.toEquiv hi).trans (φ.toEquiv.apply_symm_apply e)⟩
  labels i := (φ.lab_eq _).trans (c.labels i)
  ordered i j := (φ.eord_iff _ _).trans (c.ordered i j)

@[simp] theorem transport_status (φ : PomsetIso P Q) {U : Cube Lab k} (c : TrackCell P U) (e : Fin P.n) :
    (transport φ c).status (φ.toEquiv e) = c.status e := by
  change c.status (φ.toEquiv.symm (φ.toEquiv e)) = _
  rw [Equiv.symm_apply_apply]

@[simp] theorem transport_face (φ : PomsetIso P Q) {U V : Cube Lab k} (f : Face U V) (c : TrackCell P V) :
    transport φ (c.face f) = (transport φ c).face f := by
  apply TrackCell.status_injective
  funext a
  obtain ⟨e,rfl⟩ := φ.toEquiv.surjective a
  change (transport φ (c.face f)).status (φ.toEquiv e) = ((transport φ c).face f).status (φ.toEquiv e)
  rw [transport_status]
  by_cases he : c.status e = Status.star
  · obtain ⟨i,rfl⟩ := c.covers e he
    have h := TrackCell.face_status_occ f (transport φ c) i
    change ((transport φ c).face f).status (φ.toEquiv (c.occ i)) = f.status i at h
    rw [TrackCell.face_status_occ,h]
  · have hn : (transport φ c).status (φ.toEquiv e) ≠ Status.star := by
      simpa only [transport_status] using he
    rw [TrackCell.face_status_inactive f c he,TrackCell.face_status_inactive f (transport φ c) hn,transport_status]

def map (φ : PomsetIso P Q) : Map (track (k := k) P) (track Q) where
  app := transport φ
  natural := transport_face φ

@[simp] theorem transport_source {U V : Cube Lab k} (A B : Arrow U V) (φ : PomsetIso A.pom.val B.pom.val) :
    transport φ A.sourceCell = B.sourceCell := by
  classical
  apply TrackCell.status_injective
  funext a
  obtain ⟨e,rfl⟩ := φ.toEquiv.surjective a
  change (transport φ A.sourceCell).status (φ.toEquiv e) = B.sourceCell.status (φ.toEquiv e)
  rw [transport_status]
  change (if A.pom.val.inSrc e then Status.star else Status.zero) =
    (if B.pom.val.inSrc (φ.toEquiv e) then Status.star else Status.zero)
  rw [φ.inSrc_image_iff]

@[simp] theorem transport_target {U V : Cube Lab k} (A B : Arrow U V) (φ : PomsetIso A.pom.val B.pom.val) :
    transport φ A.targetCell = B.targetCell := by
  classical
  apply TrackCell.status_injective
  funext a
  obtain ⟨e,rfl⟩ := φ.toEquiv.surjective a
  change (transport φ A.targetCell).status (φ.toEquiv e) = B.targetCell.status (φ.toEquiv e)
  rw [transport_status]
  change (if A.pom.val.inTgt e then Status.star else Status.one) =
    (if B.pom.val.inTgt (φ.toEquiv e) then Status.star else Status.one)
  rw [φ.inTgt_image_iff]

end TrackIso

namespace Arrow
variable {U V : Cube Lab k} {Y : Precubical.{u,v} Lab k}

/-- Any genuinely pomset-labelled path determines a map from its actual track,
including labels isomorphic to the chosen ST-decomposition. -/
theorem map_of_dPom (A : Arrow U V) (x : Y.Cell U) (y : Y.Cell V)
    (h : y ∈ Y.dPom x A.pom) :
    ∃ a : Map (track A.pom.val) Y, a.app A.sourceCell = x ∧ a.app A.targetCell = y := by
  obtain ⟨p,hr,⟨φ⟩⟩ := h
  obtain ⟨a,ha,hb⟩ := Word.map_of_run p hr
  refine ⟨(TrackIso.map φ.symm).comp a,?_,?_⟩
  · change a.app (TrackIso.transport φ.symm A.sourceCell) = x
    rw [TrackIso.transport_source]
    exact ha
  · change a.app (TrackIso.transport φ.symm A.targetCell) = y
    rw [TrackIso.transport_target]
    exact hb

/-- The full path/map equivalence at an actual pomset with an ST
representation. The representation is data, not an assumed mapping property. -/
theorem mapping_iff_of_representation (A : Arrow U V) (p : Word U V)
    (hp : IntervalPomIso p.label.pom A.pom) (x : Y.Cell U) (y : Y.Cell V) :
    y ∈ Y.dPom x A.pom ↔ ∃ a : Map (track A.pom.val) Y,
      a.app A.sourceCell = x ∧ a.app A.targetCell = y := by
  constructor
  · exact map_of_dPom A x y
  · rintro ⟨a,hx,hy⟩
    obtain ⟨φ⟩ := hp
    let b := (TrackIso.map φ).comp a
    have hsrc : b.app p.label.sourceCell = x := by
      change a.app (TrackIso.transport φ p.label.sourceCell) = x
      rw [TrackIso.transport_source]
      exact hx
    have htgt : b.app p.label.targetCell = y := by
      change a.app (TrackIso.transport φ p.label.targetCell) = y
      rw [TrackIso.transport_target]
      exact hy
    exact ⟨p,(Word.lemma_3_1_b_word p x y).mpr ⟨b,hsrc,htgt⟩,⟨φ⟩⟩

end Arrow

namespace Word
variable {U V : Cube Lab k} {Y : Precubical.{u,v} Lab k}

/-- A fixed ST-decomposition determines the entire endpoint relation: any
isomorphic actual pomset label has exactly the same runs, in every HDA. -/
theorem run_iff_of_label_iso (p q : Word U V) (hpq : IntervalPomIso p.label.pom q.label.pom)
    (x : Y.Cell U) (y : Y.Cell V) : Y.Run p x y ↔ Y.Run q x y := by
  constructor
  · intro h
    exact (lemma_3_1_b_word q x y).mpr (Arrow.map_of_dPom q.label x y ⟨p,h,hpq⟩)
  · intro h
    obtain ⟨φ⟩ := hpq
    exact (lemma_3_1_b_word p x y).mpr (Arrow.map_of_dPom p.label x y ⟨q,h,⟨φ.symm⟩⟩)

end Word
end CounterFreeHDA.Cubical
