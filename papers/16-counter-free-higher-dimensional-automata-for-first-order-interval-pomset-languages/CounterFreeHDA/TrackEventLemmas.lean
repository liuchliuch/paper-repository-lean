import CounterFreeHDA.RunLabeling

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ}

namespace TrackGlue
variable {A B : PomsetData Lab} (m : GlueMatch A B)

@[simp] theorem leftEvent_lab (e : Fin A.n) :
    (glueData A B m).lab (leftEvent m e) = A.lab e := by
  change glueLab m ((index m).symm (index m _)) = _
  rw [Equiv.symm_apply_apply]
  exact glueLab_left m e

@[simp] theorem rightEvent_lab (e : Fin B.n) :
    (glueData A B m).lab (rightEvent m e) = B.lab e := by
  change glueLab m ((index m).symm (index m _)) = _
  rw [Equiv.symm_apply_apply]
  exact glueLab_right m e

theorem rightEvent_eord (hA : IsIntervalPom A) (hB : IsIntervalPom B) (e f : Fin B.n) :
    (glueData A B m).eord (rightEvent m e) (rightEvent m f) ↔ B.eord e f := by
  change glueEord m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _)) ↔ _
  rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact glueEord_right m hA hB e f

noncomputable def rightEquiv (hA : ∀ e, A.inTgt e) : Fin B.n ≃ Fin (glueData A B m).n :=
  Equiv.ofBijective (rightEvent m)
    ⟨(index m).injective.comp (GluedE.rightMap_inj _ _ _),
      (index m).surjective.comp (GluedE.rightMap_surjective m hA)⟩

end TrackGlue

namespace TrackCell
variable {P : PomsetData Lab} {U V : Cube Lab k}

theorem lower_one_iff (f : Face U V) (hl : f.Lower) (c : TrackCell P V) (e : Fin P.n) :
    (c.face f).status e = Status.one ↔ c.status e = Status.one := by
  constructor
  · intro he
    have hs := lower_status_le f hl c e
    rw [he] at hs
    have hv := (c.status e).isLt
    apply Fin.ext
    change (c.status e).val = 2
    change 2 ≤ (c.status e).val at hs
    omega
  · intro he
    rw [face_status_inactive f c (by rw [he]; decide)]
    exact he

theorem upper_zero_iff (f : Face U V) (hu : f.Upper) (c : TrackCell P V) (e : Fin P.n) :
    (c.face f).status e = Status.zero ↔ c.status e = Status.zero := by
  constructor
  · intro he
    have hs := le_upper_status f hu c e
    rw [he] at hs
    apply Fin.ext
    change (c.status e).val = 0
    change (c.status e).val ≤ 0 at hs
    omega
  · intro he
    rw [face_status_inactive f c (by rw [he]; decide)]
    exact he

end TrackCell
end CounterFreeHDA.Cubical
