import CounterFreeHDA.CornerEmbedding

/-! Extend actual corner configurations by fixing source-deleted events at
1 and target-deleted events at 0, as in the proof of Lemma 3.5. -/
namespace CounterFreeHDA.Cubical.CornerExtension
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (α : Fin P.srcLen → Status) (β : Fin P.tgtLen → Status) (hc : Corners.Compatible P α β)

noncomputable def status {U : Cube Lab k} (c : TrackCell (Corners.data P α β hc) U)
    (e : Fin P.n) : Status := by
  classical
  exact if hs : Corners.SourceDeleted P α e then Status.one else
    if ht : Corners.TargetDeleted P β e then Status.zero else
      c.status (Corners.retain P α β hc e (fun h => h.elim hs ht))

theorem status_kept {U : Cube Lab k} (c : TrackCell (Corners.data P α β hc) U)
    (e : Fin P.n) (he : ¬ Corners.Deleted P α β e) :
    status P α β hc c e = c.status (Corners.retain P α β hc e he) := by
  classical
  have hs : ¬ Corners.SourceDeleted P α e := fun h => he (Or.inl h)
  have ht : ¬ Corners.TargetDeleted P β e := fun h => he (Or.inr h)
  unfold status
  rw [dif_neg hs,dif_neg ht]

theorem status_source {U : Cube Lab k} (c : TrackCell (Corners.data P α β hc) U)
    (e : Fin P.n) (he : Corners.SourceDeleted P α e) : status P α β hc c e = Status.one := by
  classical
  exact dif_pos he

theorem status_target {U : Cube Lab k} (c : TrackCell (Corners.data P α β hc) U)
    (e : Fin P.n) (he : Corners.TargetDeleted P β e) : status P α β hc c e = Status.zero := by
  classical
  unfold status
  rw [dif_neg (fun h => Corners.deletions_disjoint P α β hc h he),dif_pos he]

@[simp] theorem status_inclusion {U : Cube Lab k} (c : TrackCell (Corners.data P α β hc) U)
    (e : Fin (Corners.data P α β hc).n) :
    status P α β hc c (Corners.inclusion P α β hc e) = c.status e := by
  rw [status_kept P α β hc c _ (Corners.inclusion_kept P α β hc e),Corners.retain_inclusion]

noncomputable def cell {U : Cube Lab k} (c : TrackCell (Corners.data P α β hc) U) : TrackCell P U where
  status := status P α β hc c
  config e f hef hf := by
    classical
    by_cases heS : Corners.SourceDeleted P α e
    · exact status_source P α β hc c e heS
    by_cases heT : Corners.TargetDeleted P β e
    · obtain ⟨i,hi,_⟩ := heT
      exact False.elim (hP.tgt_maximal e ⟨i,hi⟩ f hef)
    have he : ¬ Corners.Deleted P α β e := fun h => h.elim heS heT
    by_cases hfS : Corners.SourceDeleted P α f
    · obtain ⟨i,hi,_⟩ := hfS
      exact False.elim (hP.src_minimal f ⟨i,hi⟩ e hef)
    by_cases hfT : Corners.TargetDeleted P β f
    · exact False.elim (hf (status_target P α β hc c f hfT))
    have hf' : ¬ Corners.Deleted P α β f := fun h => h.elim hfS hfT
    have hprec : (Corners.data P α β hc).prec (Corners.retain P α β hc e he) (Corners.retain P α β hc f hf') := by
      change P.prec (Corners.inclusion P α β hc (Corners.retain P α β hc e he))
        (Corners.inclusion P α β hc (Corners.retain P α β hc f hf'))
      rw [Corners.inclusion_retain,Corners.inclusion_retain]
      exact hef
    apply (status_kept P α β hc c e he).trans
    apply c.config _ _ hprec
    exact fun h => hf ((status_kept P α β hc c f hf').trans h)
  occ i := Corners.inclusion P α β hc (c.occ i)
  inj := (Corners.inclusion P α β hc).injective.comp c.inj
  active i := (status_inclusion P α β hc c (c.occ i)).trans (c.active i)
  covers e he := by
    classical
    have heS : ¬ Corners.SourceDeleted P α e := by
      intro h
      have hh := (status_source P α β hc c e h).symm.trans he
      exact (by decide : Status.one ≠ Status.star) hh
    have heT : ¬ Corners.TargetDeleted P β e := by
      intro h
      have hh := (status_target P α β hc c e h).symm.trans he
      exact (by decide : Status.zero ≠ Status.star) hh
    have hek : ¬ Corners.Deleted P α β e := fun h => h.elim heS heT
    have hstar := (status_kept P α β hc c e hek).symm.trans he
    obtain ⟨i,hi⟩ := c.covers _ hstar
    exact ⟨i,(congrArg (Corners.inclusion P α β hc) hi).trans (Corners.inclusion_retain P α β hc e hek)⟩
  labels := c.labels
  ordered := c.ordered

@[simp] theorem cell_status_inclusion {U : Cube Lab k} (c : TrackCell (Corners.data P α β hc) U)
    (e : Fin (Corners.data P α β hc).n) :
    (cell P hP α β hc c).status (Corners.inclusion P α β hc e) = c.status e :=
  status_inclusion P α β hc c e

theorem face_status_inclusion {U V : Cube Lab k} (f : Face U V)
    (c : TrackCell (Corners.data P α β hc) V) (e : Fin (Corners.data P α β hc).n) :
    ((cell P hP α β hc c).face f).status (Corners.inclusion P α β hc e) = (c.face f).status e := by
  by_cases he : c.status e = Status.star
  · obtain ⟨i,rfl⟩ := c.covers e he
    exact (TrackCell.face_status_occ f (cell P hP α β hc c) i).trans (TrackCell.face_status_occ f c i).symm
  · have hn : (cell P hP α β hc c).status (Corners.inclusion P α β hc e) ≠ Status.star := by
      simpa only [cell_status_inclusion] using he
    rw [TrackCell.face_status_inactive f _ hn,cell_status_inclusion,TrackCell.face_status_inactive f c he]

@[simp] theorem cell_face {U V : Cube Lab k} (f : Face U V)
    (c : TrackCell (Corners.data P α β hc) V) : cell P hP α β hc (c.face f) = (cell P hP α β hc c).face f := by
  apply TrackCell.status_injective
  funext e
  classical
  by_cases heS : Corners.SourceDeleted P α e
  · have hs := status_source P α β hc c e heS
    have hn : (cell P hP α β hc c).status e ≠ Status.star := by rw [show (cell P hP α β hc c).status e = Status.one from hs]; decide
    exact (status_source P α β hc (c.face f) e heS).trans
      (hs.symm.trans (TrackCell.face_status_inactive f _ hn).symm)
  by_cases heT : Corners.TargetDeleted P β e
  · have hs := status_target P α β hc c e heT
    have hn : (cell P hP α β hc c).status e ≠ Status.star := by rw [show (cell P hP α β hc c).status e = Status.zero from hs]; decide
    exact (status_target P α β hc (c.face f) e heT).trans
      (hs.symm.trans (TrackCell.face_status_inactive f _ hn).symm)
  have he : ¬ Corners.Deleted P α β e := fun h => h.elim heS heT
  have hi := Corners.inclusion_retain P α β hc e he
  exact (status_kept P α β hc (c.face f) e he).trans
    ((face_status_inclusion P hP α β hc f c (Corners.retain P α β hc e he)).symm.trans
      (congrArg (((cell P hP α β hc c).face f).status) hi))

noncomputable def map : Map (track (k := k) (Corners.data P α β hc)) (track P) where
  app := cell P hP α β hc
  natural := cell_face P hP α β hc

end CounterFreeHDA.Cubical.CornerExtension
