import CounterFreeHDA.IdealComponents

namespace CounterFreeHDA.Cubical.OrderedPomsetRecognizer
universe u v
variable {Lab : Type u} {k : ℕ} {L : Set (IntervalPom Lab)} {h : ℕ}
    (F : OrderedPomsetRecognizer.{u,v} (k := k) L h)

noncomputable def hda : HDA Lab k := idealHDA F.C F.order F.stepImage F.J

/-- **Proposition 3.4 at actual typed endpoints.** The concrete ideal-diagram
HDA has an accepting path at P exactly when the original recognizer accepts P. -/
theorem typed_recognition {U V : Cube Lab k} (A : BoundedArrow U V) :
    (∃ (x : F.hda.Cell U) (y : F.hda.Cell V),
      F.hda.initial x ∧ F.hda.accepting y ∧ y ∈ F.hda.toPrecubical.dPom x A.pom) ↔ A.pom ∈ L := by
  classical
  constructor
  · rintro ⟨⟨S,x⟩,⟨T,y⟩,⟨hs,hi⟩,hf,p,hr,⟨φ⟩⟩
    change S = U at hs
    subst S
    obtain ⟨ht,hcomp⟩ := run_component F.C F.order F.stepImage F.J p x y hr
    subst T
    have hword := IdealDiagram.accepting_run_sound (C := F.C) (ord := F.order) (image := F.stepImage)
      hcomp hi (F.J (U := U) (V := V)) hf
    have hmem : F.map (BoundedArrow.ofWord p) ∈ F.J := by simpa only [F.wordImage_eq] using hword
    have he := F.map_iso (BoundedArrow.ofWord p) A φ
    exact (F.recognises A).mpr ((congrArg (fun a => a ∈ F.J) he).mp hmem)
  · intro ha
    let g := seedMap F.C F.order F.stepImage (track A.pom.val) A.toArrow.sourceCell
    let m := g.comp (componentInclusion F.C F.order F.stepImage F.J U)
    refine ⟨⟨U,g.app A.toArrow.sourceCell⟩,⟨U,g.app A.toArrow.targetCell⟩,?_,?_,?_⟩
    · exact ⟨rfl,seedMap_initial F.C F.order F.stepImage (track A.pom.val) A.toArrow.sourceCell⟩
    · exact F.seedMap_accepting A ha
    · apply (A.toArrow.lemma_3_1_b A.width _ _).mpr
      exact ⟨m,rfl,rfl⟩

/-- **Proposition 3.4** on every actual bounded interval pomset. -/
theorem language_iff {P : IntervalPom Lab} (hw : P.val.WidthLE k) : P ∈ F.hda.LangPom ↔ P ∈ L := by
  constructor
  · rintro ⟨U,V,x,y,hi,hf,p,hr,⟨φ⟩⟩
    let A : BoundedArrow U V := {
      pom := P
      source := φ.source_type.symm.trans p.label.source
      target := φ.target_type.symm.trans p.label.target
      width := hw }
    exact (F.typed_recognition A).mp ⟨x,y,hi,hf,p,hr,⟨φ⟩⟩
  · intro hP
    let A : BoundedArrow (sourceCube P.val (hw.source_bound P.property)) (targetCube P.val (hw.target_bound P.property)) := {
      pom := P,source := rfl,target := rfl,width := hw }
    obtain ⟨x,y,hi,hf,hr⟩ := (F.typed_recognition A).mpr hP
    exact ⟨_,_,x,y,hi,hf,hr⟩

/-- Global set equality when L is presented, as in the paper, as a language
contained in the fixed bounded-width interval-pomset source. -/
theorem language_eq (withinWidth : ∀ P ∈ L, P.val.WidthLE k) : F.hda.LangPom = L := by
  ext P
  constructor
  · intro hP
    exact (F.language_iff (F.hda.accepted_width hP)).mp hP
  · intro hP
    exact (F.language_iff (withinWidth P hP)).mpr hP

end CounterFreeHDA.Cubical.OrderedPomsetRecognizer
