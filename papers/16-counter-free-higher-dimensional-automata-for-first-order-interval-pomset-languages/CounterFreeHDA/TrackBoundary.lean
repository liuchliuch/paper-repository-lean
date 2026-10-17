import CounterFreeHDA.Track

/-! Distinguished cubes of B(P) and the obstruction for incompatible faces
in Lemma 3.5. All reachability statements refer to actual labelled runs. -/

namespace CounterFreeHDA.Cubical

universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab)

def sourceCube (hs : P.srcLen ≤ k) : Cube Lab k :=
  ⟨⟨P.srcLen, by omega⟩, P.lab ∘ P.src⟩
def targetCube (ht : P.tgtLen ≤ k) : Cube Lab k :=
  ⟨⟨P.tgtLen, by omega⟩, P.lab ∘ P.tgt⟩

noncomputable def iota (hP : IsIntervalPom P) (hs : P.srcLen ≤ k) :
    TrackCell P (sourceCube P hs) := by
  classical
  exact {
    status e := if P.inSrc e then Status.star else Status.zero
    config e f hef hf := by
      have hin : P.inSrc f := by by_contra h; exact hf (if_neg h)
      exact False.elim (hP.src_minimal f hin e hef)
    occ := P.src
    inj := P.src_inj
    active i := if_pos ⟨i,rfl⟩
    covers e he := by
      by_cases h : P.inSrc e
      · exact h
      · rw [if_neg h] at he
        exact False.elim ((by decide : Status.zero ≠ Status.star) he)
    labels _ := rfl
    ordered := hP.src_eord }

noncomputable def tau (hP : IsIntervalPom P) (ht : P.tgtLen ≤ k) :
    TrackCell P (targetCube P ht) := by
  classical
  exact {
    status e := if P.inTgt e then Status.star else Status.one
    config e f hef _ := by
      by_cases h : P.inTgt e
      · exact False.elim (hP.tgt_maximal e h f hef)
      · exact if_neg h
    occ := P.tgt
    inj := P.tgt_inj
    active i := if_pos ⟨i,rfl⟩
    covers e he := by
      by_cases h : P.inTgt e
      · exact h
      · rw [if_neg h] at he
        exact False.elim ((by decide : Status.one ≠ Status.star) he)
    labels _ := rfl
    ordered := hP.tgt_eord }

namespace TrackCell
variable {P} {U V : Cube Lab k}

theorem lower_status_le (f : Face U V) (hl : f.Lower) (c : TrackCell P V) (e : Fin P.n) :
    (c.face f).status e ≤ c.status e := by
  by_cases he : c.status e = Status.star
  · obtain ⟨i,rfl⟩ := c.covers e he
    rw [face_status_occ, c.active]
    cases hs : f.sub i with
    | inl j => simp only [Face.status, hs]; exact le_refl _
    | inr b => have hb := hl i b hs; subst b; simpa only [Face.status, hs] using Status.zero_le_star
  · rw [face_status_inactive f c he]

theorem le_upper_status (f : Face U V) (hu : f.Upper) (c : TrackCell P V) (e : Fin P.n) :
    c.status e ≤ (c.face f).status e := by
  by_cases he : c.status e = Status.star
  · obtain ⟨i,rfl⟩ := c.covers e he
    rw [face_status_occ, c.active]
    cases hs : f.sub i with
    | inl j => simp only [Face.status, hs]; exact le_refl _
    | inr b => have hb := hu i b hs; subst b; simpa only [Face.status, hs] using Status.star_le_one
  · rw [face_status_inactive f c he]

/-- Statuses can only increase along the actual characteristic face graph. -/
theorem run_status_mono {p : Word U V} {x : TrackCell P U} {y : TrackCell P V}
    (r : (track P).Run p x y) (e : Fin P.n) : x.status e ≤ y.status e := by
  induction p with
  | nil U =>
    have hxy := ((track P).run_nil_iff x y).mp r
    subst y
    exact le_refl _
  | cons s p ih =>
    cases s with
    | start f hl hd =>
      obtain ⟨z,hxz,hr⟩ := ((track P).run_start_iff f hl hd p x y).mp r
      subst x
      exact le_trans (lower_status_le f hl z e) (ih hr)
    | stop f hu hd =>
      have hr := ((track P).run_stop_iff f hu hd p x y).mp r
      exact le_trans (le_upper_status f hu x e) (ih hr)

end TrackCell

/-- **Lemma 3.5, incompatible case.** Source and target faces disagreeing
backwards on a shared interface event admit no directed path at any label. -/
theorem lemma_3_5_incompatible
    (hP : IsIntervalPom P) (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k)
    {U V : Cube Lab k} (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (hincompatible : ∃ i j, P.src i = P.tgt j ∧ ¬ α.status i ≤ β.status j)
    (p : Word U V) :
    ¬ (track P).Run p ((iota P hP hs).face α) ((tau P hP ht).face β) := by
  intro r
  obtain ⟨i,j,he,hnot⟩ := hincompatible
  have h := TrackCell.run_status_mono r (P.src i)
  have hα := TrackCell.face_status_occ α (iota P hP hs) i
  have hβ := TrackCell.face_status_occ β (tau P hP ht) j
  change ((iota P hP hs).face α).status (P.src i) = α.status i at hα
  change ((tau P hP ht).face β).status (P.tgt j) = β.status j at hβ
  rw [hα,he,hβ] at h
  exact hnot h

end CounterFreeHDA.Cubical
