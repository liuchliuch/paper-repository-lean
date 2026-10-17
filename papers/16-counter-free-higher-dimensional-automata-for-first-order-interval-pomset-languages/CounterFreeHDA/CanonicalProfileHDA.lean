import CounterFreeHDA.FullProfileCompletion

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

abbrev LiveActualProfile (U : UCube) := {x : ActualProfile U // liveCode U x.val}

noncomputable def profileIndex (U : UCube) : Fin (Completion.profileSize U.1) ≃ LiveActualProfile U :=
  Equiv.ofBijective (fun i => ⟨templateProfile U i,templateCode_live U i⟩) (by
    constructor
    · intro i j h
      exact templateCode_injective U (congrArg (fun x : LiveActualProfile U => x.val.val) h)
    · rintro ⟨⟨c,P,hP⟩,hl⟩
      obtain ⟨i,hi⟩ := live_profile_exhaustive P (hP.symm ▸ hl)
      refine ⟨i,?_⟩
      apply Subtype.ext
      apply Subtype.ext
      exact hi.symm.trans hP)

noncomputable def profileEquiv (U : UCube) : LiveActualProfile U ≃ Completion.completionHDA.Cell U :=
  (profileIndex U).symm.trans (Completion.cellEquiv U)

noncomputable def canonicalProfileHDA : HDA Unit 2 where
  Cell := LiveActualProfile
  face f x := (profileEquiv _).symm (Completion.completionHDA.face f (profileEquiv _ x))
  face_ident x := by simp only [Completion.completionHDA.face_ident,Equiv.symm_apply_apply]
  face_comp f g x := by
    simp only [Equiv.apply_symm_apply,Completion.completionHDA.face_comp]
  initial x := Completion.completionHDA.initial (profileEquiv _ x)
  accepting x := Completion.completionHDA.accepting (profileEquiv _ x)

/-- This is an HDA of actual semantic deletion profiles, with every
precubical identity. Its finite presentation is the displayed ten-cell HDA. -/
noncomputable def canonicalMap : Map canonicalProfileHDA.toPrecubical Completion.completionHDA.toPrecubical where
  app := (profileEquiv _)
  natural f x := Equiv.apply_symm_apply _ _

noncomputable def canonicalInverse : Map Completion.completionHDA.toPrecubical canonicalProfileHDA.toPrecubical where
  app := (profileEquiv _).symm
  natural f x := by simp only [canonicalProfileHDA,Equiv.apply_symm_apply]

theorem profileEquiv_index (U : UCube) (i : Fin (Completion.profileSize U.1)) :
    profileEquiv U (profileIndex U i) = Completion.indexCell U i := by
  change (Completion.cellEquiv U) ((profileIndex U).symm (profileIndex U i)) = _
  rw [Equiv.symm_apply_apply]
  rfl

/-- In the actual semantic HDA a lower face is precisely restriction to
coordinates deleting the specified events. -/
theorem canonical_lower {U V : UCube} (f : Cubical.Face U V) (hf : f.Lower) (x : LiveActualProfile V) :
    (canonicalProfileHDA.face f x).val.val = lowerCode f x.val.val := by
  obtain ⟨i,rfl⟩ := (profileIndex V).surjective x
  obtain ⟨j,hcode,hface⟩ := lower_profile_faces U V f hf i
  change ((profileEquiv U).symm (Completion.completionHDA.face f (profileEquiv V (profileIndex V i)))).val.val = _
  rw [profileEquiv_index,hface,← profileEquiv_index U j,Equiv.symm_apply_apply]
  exact hcode.symm

/-- Every elementary upper face is the actual prefix termination update,
whose semantic correctness was derived from real deletion/gluing. -/
theorem canonical_upper {U V : UCube} (f : Cubical.Face U V) (hf : f.Upper) (hd : V.dim = U.dim+1)
    (x : LiveActualProfile V) :
    (canonicalProfileHDA.face f x).val.val = updateCode (.stop f hf hd) x.val.val := by
  obtain ⟨i,rfl⟩ := (profileIndex V).surjective x
  obtain ⟨j,hcode,hface⟩ := upper_profile_faces U V f hf hd i
  change ((profileEquiv U).symm (Completion.completionHDA.face f (profileEquiv V (profileIndex V i)))).val.val = _
  rw [profileEquiv_index,hface,← profileEquiv_index U j,Equiv.symm_apply_apply]
  exact hcode.symm

theorem canonical_language_eq : canonicalProfileHDA.LangPom = Completion.completionHDA.LangPom := by
  ext P
  constructor
  · rintro ⟨U,V,x,y,hx,hy,p,hr,hi⟩
    exact ⟨U,V,profileEquiv U x,profileEquiv V y,hx,hy,p,canonicalMap.map_run hr,hi⟩
  · rintro ⟨U,V,x,y,hx,hy,p,hr,hi⟩
    refine ⟨U,V,(profileEquiv U).symm x,(profileEquiv V).symm y,?_,?_,p,canonicalInverse.map_run hr,hi⟩
    · change Completion.completionHDA.initial (profileEquiv U ((profileEquiv U).symm x))
      simpa only [Equiv.apply_symm_apply] using hx
    · change Completion.completionHDA.accepting (profileEquiv V ((profileEquiv V).symm y))
      simpa only [Equiv.apply_symm_apply] using hy

theorem canonical_not_counterFree : ¬ canonicalProfileHDA.toPrecubical.CounterFreePom := by
  rintro ⟨N,hN,H⟩
  apply Completion.completion_not_counterFreePom
  refine ⟨N,hN,?_⟩
  intro U x P
  ext y
  have he : ∀ n, y ∈ Completion.completionHDA.toPrecubical.dPom x (P.pow n).pom ↔
      (profileEquiv U).symm y ∈ canonicalProfileHDA.toPrecubical.dPom ((profileEquiv U).symm x) (P.pow n).pom := by
    intro n
    constructor
    · rintro ⟨p,hr,hi⟩; exact ⟨p,canonicalInverse.map_run hr,hi⟩
    · rintro ⟨p,hr,hi⟩
      have hmap := canonicalMap.map_run hr
      simp only [canonicalMap,Equiv.apply_symm_apply] at hmap
      exact ⟨p,hmap,hi⟩
  exact (he N).trans (((congrArg (fun s => (profileEquiv U).symm y ∈ s)
    (H U ((profileEquiv U).symm x) P)).to_iff).trans (he (N+1)).symm)

end CounterFreeHDA.Appendix.Residual

namespace CounterFreeHDA.Appendix.Residual
open Cubical Compare

theorem canonical_markings {U : UCube} (x : LiveActualProfile U) :
    (canonicalProfileHDA.initial x ↔ U.dim = 0 ∧ x.val.val ∅ = 0) ∧
    (canonicalProfileHDA.accepting x ↔ U.dim = 0 ∧ (x.val.val ∅ = 0 ∨ x.val.val ∅ = 2)) := by
  have h : ∀ (U : UCube) (i : Fin (Completion.profileSize U.1)),
      (Completion.completionHDA.initial (Completion.indexCell U i) ↔ U.dim = 0 ∧ templateCode U i ∅ = 0) ∧
      (Completion.completionHDA.accepting (Completion.indexCell U i) ↔ U.dim = 0 ∧
        (templateCode U i ∅ = 0 ∨ templateCode U i ∅ = 2)) := by
    dsimp only [Completion.completionHDA,Completion.indexCell]
    decide
  obtain ⟨i,rfl⟩ := (profileIndex U).surjective x
  change (Completion.completionHDA.initial (profileEquiv U (profileIndex U i)) ↔ _) ∧
    (Completion.completionHDA.accepting (profileEquiv U (profileIndex U i)) ↔ _)
  rw [profileEquiv_index]
  exact h U i

/-- Every cell coordinate is an actual suffix language of an actual event
deletion of a prefix. No residual or deletion conclusion is an HDA input. -/
theorem canonical_coordinate_semantics {U : UCube} (x : LiveActualProfile U) :
    ∃ P : Prefix U, ∀ D : Finset (Fin U.dim),
      embedKind (profile P D) = x.val.val D ∧
      residualLanguage (Cubical.Face.activeCube U (deletionStatus U D)) (profile P D) =
        prefixResidual (deletedPrefix P D) := by
  obtain ⟨P,hP⟩ := x.val.property
  exact ⟨P,fun D => ⟨congrFun hP D,profile_semantics P D⟩⟩

end CounterFreeHDA.Appendix.Residual
