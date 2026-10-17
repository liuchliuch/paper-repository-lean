import CounterFreeHDA.TypedGlue

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ} {U V : Cube Lab k}

namespace Step

theorem start_target_full (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1)
    (e : Fin (label (.start f hl hd)).pom.n) :
    (label (.start f hl hd)).targetCell.status e = Status.star := by
  classical
  exact if_pos ⟨e,rfl⟩

theorem stop_source_full (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1)
    (e : Fin (label (.stop f hu hd)).pom.n) :
    (label (.stop f hu hd)).sourceCell.status e = Status.star := by
  classical
  exact if_pos ⟨e,rfl⟩

/-- The lower face of the actual starter's full cube is its initial cell. -/
theorem start_source_face (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1) :
    (label (.start f hl hd)).sourceCell = (label (.start f hl hd)).targetCell.face f := by
  classical
  apply TrackCell.status_injective
  funext e
  change (label (.start f hl hd)).sourceCell.status e =
    ((label (.start f hl hd)).targetCell.face f).status e
  have h := TrackCell.face_status_occ f (label (.start f hl hd)).targetCell e
  change ((label (.start f hl hd)).targetCell.face f).status e = f.status e at h
  rw [h]
  cases hs : f.sub e with
  | inl i =>
    have hin : (label (.start f hl hd)).pom.val.inSrc e := ⟨i,(f.position_unique hs).symm⟩
    change (if (label (.start f hl hd)).pom.val.inSrc e then Status.star else Status.zero) = _
    rw [if_pos hin]
    simp only [Face.status,hs]
  | inr b =>
    have hb := hl e b hs
    subst b
    have hnot : ¬ (label (.start f hl hd)).pom.val.inSrc e := by
      rintro ⟨i,hi⟩
      change f.position i = e at hi
      have hh := f.position_spec i
      rw [hi,hs] at hh
      cases hh
    change (if (label (.start f hl hd)).pom.val.inSrc e then Status.star else Status.zero) = _
    rw [if_neg hnot]
    simp only [Face.status,hs]

/-- The upper face of the actual terminator's full cube is its final cell. -/
theorem stop_target_face (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1) :
    (label (.stop f hu hd)).targetCell = (label (.stop f hu hd)).sourceCell.face f := by
  classical
  apply TrackCell.status_injective
  funext e
  change (label (.stop f hu hd)).targetCell.status e =
    ((label (.stop f hu hd)).sourceCell.face f).status e
  have h := TrackCell.face_status_occ f (label (.stop f hu hd)).sourceCell e
  change ((label (.stop f hu hd)).sourceCell.face f).status e = f.status e at h
  rw [h]
  cases hs : f.sub e with
  | inl i =>
    have hin : (label (.stop f hu hd)).pom.val.inTgt e := ⟨i,(f.position_unique hs).symm⟩
    change (if (label (.stop f hu hd)).pom.val.inTgt e then Status.star else Status.one) = _
    rw [if_pos hin]
    simp only [Face.status,hs]
  | inr b =>
    have hb := hu e b hs
    subst b
    have hnot : ¬ (label (.stop f hu hd)).pom.val.inTgt e := by
      rintro ⟨i,hi⟩
      change f.position i = e at hi
      have hh := f.position_spec i
      rw [hi,hs] at hh
      cases hh
    change (if (label (.stop f hu hd)).pom.val.inTgt e then Status.star else Status.one) = _
    rw [if_neg hnot]
    simp only [Face.status,hs]

variable {Y : Precubical.{u,v} Lab k}

noncomputable def startMap (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1) (y : Y.Cell V) :
    Map (track (label (.start f hl hd)).pom.val) Y :=
  mapFromFull (label (.start f hl hd)).targetCell (start_target_full f hl hd) y

noncomputable def stopMap (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1) (x : Y.Cell U) :
    Map (track (label (.stop f hu hd)).pom.val) Y :=
  mapFromFull (label (.stop f hu hd)).sourceCell (stop_source_full f hu hd) x

@[simp] theorem startMap_target (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1) (y : Y.Cell V) :
    (startMap f hl hd y).app (label (.start f hl hd)).targetCell = y := mapFromFull_top _ _ _

@[simp] theorem startMap_source (f : Face U V) (hl : f.Lower) (hd : V.dim = U.dim + 1) (y : Y.Cell V) :
    (startMap f hl hd y).app (label (.start f hl hd)).sourceCell = Y.face f y := by
  rw [start_source_face]
  exact ((startMap f hl hd y).natural f _).trans (congrArg (Y.face f) (startMap_target f hl hd y))

@[simp] theorem stopMap_source (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1) (x : Y.Cell U) :
    (stopMap f hu hd x).app (label (.stop f hu hd)).sourceCell = x := mapFromFull_top _ _ _

@[simp] theorem stopMap_target (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1) (x : Y.Cell U) :
    (stopMap f hu hd x).app (label (.stop f hu hd)).targetCell = Y.face f x := by
  rw [stop_target_face]
  exact ((stopMap f hu hd x).natural f _).trans (congrArg (Y.face f) (stopMap_source f hu hd x))

theorem canonicalRun (s : Step U V) :
    (track s.label.pom.val).Run (.cons s (.nil V)) s.label.sourceCell s.label.targetCell := by
  cases s with
  | start f hl hd =>
    rw [start_source_face]
    exact Precubical.Run.start f hl hd (.nil _)
  | stop f hu hd =>
    rw [stop_target_face]
    exact Precubical.Run.stop f hu hd (.nil _)

end Step

namespace Arrow

theorem identity_full (U : Cube Lab k) (e : Fin (ident U).pom.n) :
    (ident U).sourceCell.status e = Status.star := by
  classical
  exact if_pos ⟨e,rfl⟩

@[simp] theorem identity_source_target (U : Cube Lab k) : (ident U).sourceCell = (ident U).targetCell := by
  classical
  apply TrackCell.status_injective
  funext e
  change (ident U).sourceCell.status e = (ident U).targetCell.status e
  rw [identity_full]
  exact (if_pos ⟨e,rfl⟩).symm

end Arrow
end CounterFreeHDA.Cubical
