import CounterFreeHDA.Reachability

namespace CounterFreeHDA.Cubical.Word
universe u
variable {Lab : Type u} {k : ℕ} {U V W : Cube Lab k}

noncomputable def appendLabelIso (p : Word U V) (q : Word V W) :
    PomsetIso (p.append q).label.pom.val (p.label.comp q.label).pom.val := by
  induction p with
  | nil U => exact (BoundedArrow.ofWord q).identityLeftIso.symm
  | cons s p ih =>
    exact (BoundedArrow.compIso (A := BoundedArrow.ofStep s) (A' := BoundedArrow.ofStep s)
      (B := BoundedArrow.ofWord (p.append q)) (B' := (BoundedArrow.ofWord p).comp (BoundedArrow.ofWord q))
      (PomsetIso.refl s.label.pom.val) (ih q)).trans
      (BoundedArrow.assocIso (BoundedArrow.ofStep s) (BoundedArrow.ofWord p) (BoundedArrow.ofWord q)).symm

end CounterFreeHDA.Cubical.Word
