import CounterFreeHDA.Size

/-! Faces in the actual characteristic HDA are exactly replacements of active
statuses. This supplies the concrete atlas used to glue characteristic maps. -/

namespace CounterFreeHDA.Cubical
universe u v
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab}

namespace TrackCell
variable {U V : Cube Lab k}

/-- The proposed face has c's status on each active coordinate of d. -/
noncomputable def faceSub (c : TrackCell P U) (d : TrackCell P V) (j : Fin V.dim) :
    Fin U.dim ⊕ Bool := by
  classical
  exact if h : c.status (d.occ j) = Status.star then
    .inl (c.oldPosition (d.occ j) h) else .inr (decide (c.status (d.occ j) = Status.one))

theorem faceSub_inl_iff (c : TrackCell P U) (d : TrackCell P V) (j : Fin V.dim) (i : Fin U.dim) :
    faceSub c d j = Sum.inl i ↔ d.occ j = c.occ i := by
  classical
  unfold faceSub
  split_ifs with h
  · constructor
    · intro he
      exact (c.oldPosition_spec _ h).symm.trans (congrArg c.occ (Sum.inl.inj he))
    · intro he
      apply congrArg Sum.inl
      exact c.inj ((c.oldPosition_spec _ h).trans he)
  · constructor
    · intro he; cases he
    · intro he
      exact False.elim (h (he ▸ c.active i))

private theorem inactive_code (s : Status) (h : s ≠ Status.star) :
    (if s = Status.one then Status.one else Status.zero) = s := by
  fin_cases s
  · decide
  · exact False.elim (h rfl)
  · decide

/-- A configuration c is a face of d iff every inactive event of d is
unchanged. The actual face, with ordered variable names, is constructed. -/
noncomputable def faceFrom (c : TrackCell P U) (d : TrackCell P V)
    (hd : ∀ e, d.status e ≠ Status.star → c.status e = d.status e) : Face U V where
  sub := faceSub c d
  vars i := by
    have hactive : d.status (c.occ i) = Status.star := by
      by_contra h
      exact h ((hd _ h).symm.trans (c.active i))
    let j := d.oldPosition (c.occ i) hactive
    refine ⟨j,(faceSub_inl_iff c d j i).mpr (d.oldPosition_spec _ hactive),?_⟩
    intro l hl
    apply d.inj
    exact ((faceSub_inl_iff c d l i).mp hl).trans (d.oldPosition_spec _ hactive).symm
  ordered := by
    intro a b i j hab hai hbj
    have hi := (faceSub_inl_iff c d a i).mp hai
    have hj := (faceSub_inl_iff c d b j).mp hbj
    have h := (d.ordered a b).mpr hab
    rw [hi,hj] at h
    exact (c.ordered i j).mp h
  labels := by
    intro j i hji
    have he := (faceSub_inl_iff c d j i).mp hji
    exact (d.labels j).symm.trans ((congrArg P.lab he).trans (c.labels i))

@[simp] theorem faceFrom_face (c : TrackCell P U) (d : TrackCell P V)
    (hd : ∀ e, d.status e ≠ Status.star → c.status e = d.status e) :
    d.face (faceFrom c d hd) = c := by
  classical
  apply TrackCell.ext
  · funext e
    by_cases he : d.status e = Status.star
    · obtain ⟨j,rfl⟩ := d.covers e he
      rw [face_status_occ]
      change (match faceSub c d j with
        | .inl _ => Status.star | .inr false => Status.zero | .inr true => Status.one) = _
      unfold faceSub
      split_ifs with hc
      · exact hc.symm
      · cases hb : decide (c.status (d.occ j) = Status.one)
        · have ht := of_decide_eq_false hb
          simpa only [if_neg ht] using inactive_code _ hc
        · exact (of_decide_eq_true hb).symm
    · rw [face_status_inactive _ _ he]
      exact (hd e he).symm
  · funext i
    exact (faceSub_inl_iff c d _ i).mp ((faceFrom c d hd).position_spec i)

theorem face_injective (d : TrackCell P V) :
    Function.Injective (fun f : Face U V => d.face f) := by
  intro f g h
  have hs : f.status = g.status := by
    funext j
    have hj := congrArg (fun c : TrackCell P U => c.status (d.occ j)) h
    simpa only [face_status_occ] using hj
  have hf := Face.total_status_injective V (a₁ := ⟨U,f⟩) (a₂ := ⟨U,g⟩) hs
  simpa only [Sigma.mk.inj_iff,heq_eq_eq,true_and] using hf

theorem exists_face_iff (c : TrackCell P U) (d : TrackCell P V) :
    (∃ f : Face U V, d.face f = c) ↔
      ∀ e, d.status e ≠ Status.star → c.status e = d.status e := by
  constructor
  · rintro ⟨f,rfl⟩ e he
    exact face_status_inactive f d he
  · intro hd
    exact ⟨faceFrom c d hd,faceFrom_face c d hd⟩

end TrackCell

/-- The standard labelled cube as a representable precubical set. -/
def standardCube (U : Cube Lab k) : Precubical Lab k where
  Cell V := Face V U
  face f g := f.comp g
  face_ident := Face.ident_comp
  face_comp f g h := (Face.assoc f g h).symm

/-- Each actual characteristic cell gives its full face cube. -/
noncomputable def cellCube {U : Cube Lab k} (d : TrackCell P U) : Map (standardCube U) (track P) where
  app f := d.face f
  natural f g := (d.face_comp f g).symm

/-- A chosen cell in any HDA determines a cubical map on its standard cube. -/
def cubeMap {Y : Precubical.{u,v} Lab k} {U : Cube Lab k} (y : Y.Cell U) :
    Map (standardCube U) Y where
  app f := Y.face f y
  natural f g := (Y.face_comp f g y).symm

end CounterFreeHDA.Cubical
