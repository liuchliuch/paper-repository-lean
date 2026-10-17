import CounterFreeHDA.CornerSupport

namespace CounterFreeHDA.Cubical
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {U V : Cube Lab k}
    (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (hc : Corners.Compatible P α.status β.status)

/-- **Lemma 3.5, compatible case.** Actual path labels between boundary
faces are exactly subsumptions of the induced corner pomset. -/
theorem lemma_3_5_compatible (A : Arrow U V) (hw : A.pom.val.WidthLE k) :
    ((tau P hP ht).face β) ∈ (track P).dPom ((iota P hP hs).face α) A.pom ↔
      A.pom ⊑ₛ (CornerFaces.arrow P hP hs ht α β hc).pom := by
  classical
  let C := CornerFaces.arrow P hP hs ht α β hc
  let M := CornerExtension.map (k := k) P hP α.status β.status hc
  constructor
  · rintro ⟨p,hr,⟨φ⟩⟩
    have hsub : p.label.pom ⊑ₛ C.pom := by
      apply RunLabeling.restrict_subsumption C p (RunLabeling.ofRun hr)
        (Corners.inclusion P α.status β.status hc)
      · intro e; rfl
      · intro e f; exact Iff.rfl
      · intro e f; exact Iff.rfl
      · exact corner_support P hP hs ht α β hc
      · intro i
        exact congrArg (fun c : TrackCell P U => c.occ i) (CornerFaces.extension_source P hP hs ht α β hc)
      · intro i
        exact congrArg (fun c : TrackCell P V => c.occ i) (CornerFaces.extension_target P hP hs ht α β hc)
    exact subsumption_trans φ.symm.subsumption hsub
  · intro h
    obtain ⟨p,hr,hp⟩ := Refinement.complete_path A C h hw
    have hm := M.map_run hr
    change (track P).Run p (CornerExtension.cell P hP α.status β.status hc C.sourceCell)
      (CornerExtension.cell P hP α.status β.status hc C.targetCell) at hm
    rw [CornerFaces.extension_source,CornerFaces.extension_target] at hm
    exact ⟨p,hm,hp⟩

/-- The maximal compatible-corner label itself is realized between the
actual boundary faces, with no assumed path-existence premise. -/
theorem corner_complete_path (hw : P.WidthLE k) :
    ((tau P hP ht).face β) ∈ (track P).dPom ((iota P hP hs).face α)
      (CornerFaces.arrow P hP hs ht α β hc).pom := by
  let C := CornerFaces.arrow P hP hs ht α β hc
  have hwidth : C.pom.val.WidthLE k := hw.ofEmbedding (Corners.inclusion P α.status β.status hc) (fun _ _ h => h)
  exact (lemma_3_5_compatible P hP hs ht α β hc C hwidth).mpr (subsumption_refl C.pom)

end CounterFreeHDA.Cubical
