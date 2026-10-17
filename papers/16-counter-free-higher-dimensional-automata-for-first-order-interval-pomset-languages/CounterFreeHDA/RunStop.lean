import CounterFreeHDA.RunStopAtlas

namespace CounterFreeHDA.Cubical.RunLabeling
universe u
variable {Lab : Type u} {k : ℕ} {P : PomsetData Lab} {U V W : Cube Lab k}

noncomputable def stop (f : Face V U) (hu : f.Upper) (hd : U.dim = V.dim + 1)
    (p : Word V W) (x : TrackCell P U) (y : TrackCell P W)
    (R : RunLabeling p (x.face f) y) (hxy : ∀ e, x.status e ≤ y.status e) :
    RunLabeling (.cons (.stop f hu hd) p) x y := by
  classical
  let m := Stop.matching f hu hd p
  let G := Stop.atlas f hu hd p x y R
  exact {
    event := G.embedding
    labels e := Stop.raw_labels f hu hd p x y R _
    source i := G.embedding_left i
    target i := (G.embedding_right (p.label.pom.tgt i)).trans (R.target i)
    support e := by
      change (∃ a, G.embedding a = e) ↔ _
      rw [G.range_iff]
      change (∃ a, x.occ a = e) ∨ (∃ b, R.event b = e) ↔ _
      have hact : (∃ a, x.occ a = e) ↔ x.status e = Status.star := by
        constructor
        · rintro ⟨a,rfl⟩; exact x.active a
        · exact x.covers e
      rw [hact,R.support]
      by_cases ha : x.status e = Status.star
      · have hn : x.status e ≠ Status.one := by rw [ha]; decide
        have hy : y.status e ≠ Status.zero := by
          intro he
          have h := hxy e
          rw [ha,he] at h
          exact (by decide : ¬ Status.star ≤ Status.zero) h
        exact iff_of_true (Or.inl ha) ⟨hn,hy⟩
      · rw [TrackCell.face_status_inactive f x ha]
        simp only [ha,false_or]
    precedence e g h := Stop.raw_precedence f hu hd p x y R _ _ h
    order e g heg hge := Stop.raw_order f hu hd p x y R _ _ heg hge }

/-- Every actual run yields an event-injective realization of its full
pomset label, with precisely the events met by the path. -/
theorem exists_of_run {p : Word U V} {x : TrackCell P U} {y : TrackCell P V}
    (hr : (track P).Run p x y) : Nonempty (RunLabeling p x y) := by
  induction p with
  | nil U =>
    have hxy := ((track P).run_nil_iff x y).mp hr
    subst y
    exact ⟨RunLabeling.nil x⟩
  | cons s p ih =>
    cases s with
    | start f hl hd =>
      obtain ⟨z,hxz,hrest⟩ := ((track P).run_start_iff f hl hd p x y).mp hr
      subst x
      obtain ⟨R⟩ := ih hrest
      exact ⟨start f hl hd p z y R⟩
    | stop f hu hd =>
      have hrest := ((track P).run_stop_iff f hu hd p x y).mp hr
      obtain ⟨R⟩ := ih hrest
      exact ⟨stop f hu hd p x y R (fun e => TrackCell.run_status_mono hr e)⟩

noncomputable def ofRun {p : Word U V} {x : TrackCell P U} {y : TrackCell P V}
    (hr : (track P).Run p x y) : RunLabeling p x y := Classical.choice (exists_of_run hr)

end CounterFreeHDA.Cubical.RunLabeling
