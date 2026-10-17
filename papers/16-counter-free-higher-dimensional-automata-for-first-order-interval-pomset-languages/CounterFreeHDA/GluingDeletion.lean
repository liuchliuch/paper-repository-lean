import CounterFreeHDA.GluingDeletionPlan

namespace CounterFreeHDA.Deletion.Plan
universe u
open Cubical.TrackGlue
variable {Lab : Type u} {A B : PomsetData Lab} {m : GlueMatch A B} (D : Plan m)

private theorem overlap (e : Fin D.leftData.n) (f : Fin D.rightData.n) (hef : D.left e = D.right f) :
    ∃ i : Fin D.leftData.tgtLen, D.leftData.tgt i = e ∧
      D.rightData.src (Fin.cast D.glueMatch.len_eq i) = f := by
  have hold : leftEvent m (inclusion A D.keepA e) = rightEvent m (inclusion B D.keepB f) :=
    (D.inclusion_left e).symm.trans ((congrArg (inclusion (glueData A B m) D.keepG) hef).trans (D.inclusion_right f))
  obtain ⟨j,hjA,hjB⟩ := (glued_identified_iff m.len_eq _ _).mp ((index m).injective hold)
  have hk : D.keepA (A.tgt j) := hjA.symm ▸ inclusion_kept A D.keepA e
  have hm : j ∈ target A D.keepA := Finset.mem_filter.mpr ⟨Finset.mem_univ j,hk⟩
  let i := (target A D.keepA).orderIsoOfFin rfl |>.symm ⟨j,hm⟩
  have hpos : (target A D.keepA).orderEmbOfFin rfl i = j :=
    congrArg Subtype.val ((target A D.keepA).orderIsoOfFin rfl |>.apply_symm_apply ⟨j,hm⟩)
  refine ⟨i,(inclusion A D.keepA).injective ?_,(inclusion B D.keepB).injective ?_⟩
  · exact (inclusion_target A D.keepA i).trans ((congrArg A.tgt hpos).trans hjA)
  · have hi := (D.positions i).symm.trans (congrArg (Fin.cast m.len_eq) hpos)
    exact (inclusion_source B D.keepB _).trans ((congrArg B.src hi).trans hjB)

private theorem cover (e : Fin D.gluedData.n) :
    (∃ a, D.left a = e) ∨ (∃ b, D.right b = e) := by
  rcases event_cover m (inclusion (glueData A B m) D.keepG e) with ⟨a,ha⟩ | ⟨b,hb⟩
  · have hk : D.keepA a := (D.left_iff a).mp (ha.symm ▸ inclusion_kept (glueData A B m) D.keepG e)
    refine Or.inl ⟨retain A D.keepA a hk,(inclusion (glueData A B m) D.keepG).injective ?_⟩
    exact (D.inclusion_left _).trans ((congrArg (leftEvent m) (inclusion_retain A D.keepA a hk)).trans ha)
  · have hk : D.keepB b := (D.right_iff b).mp (hb.symm ▸ inclusion_kept (glueData A B m) D.keepG e)
    refine Or.inr ⟨retain B D.keepB b hk,(inclusion (glueData A B m) D.keepG).injective ?_⟩
    exact (D.inclusion_right _).trans ((congrArg (rightEvent m) (inclusion_retain B D.keepB b hk)).trans hb)

private theorem cross (e : Fin D.leftData.n) (f : Fin D.rightData.n)
    (he : ¬ D.leftData.inTgt e) (hf : ¬ D.rightData.inSrc f) : D.gluedData.prec (D.left e) (D.right f) := by
  classical
  have he' : ¬ A.inTgt (inclusion A D.keepA e) := fun h => he ((inTgt_iff A D.keepA e).mpr h)
  have hf' : ¬ B.inSrc (inclusion B D.keepB f) := fun h => hf ((inSrc_iff B D.keepB f).mpr h)
  have hp : (glueData A B m).prec (leftEvent m (inclusion A D.keepA e)) (rightEvent m (inclusion B D.keepB f)) := by
    change gluePrec m.len_eq ((index m).symm (index m _)) ((index m).symm (index m _))
    rw [Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    unfold GluedE.leftMap GluedE.rightMap
    rw [dif_neg he',dif_neg hf']
    trivial
  exact (congrArg₂ (glueData A B m).prec (D.inclusion_left e) (D.inclusion_right f)).mpr hp

/-- Realize the reduced-factor gluing inside the induced deletion of the
original product, checking exact overlap, coverage, both orders and interfaces. -/
noncomputable def realization (hA : IsIntervalPom A) (hB : IsIntervalPom B) :
    GluingRealization D.glueMatch D.gluedData where
  left := D.left
  right := D.right
  left_lab e := (congrArg (glueData A B m).lab (D.inclusion_left e)).trans (leftEvent_lab m _)
  right_lab e := (congrArg (glueData A B m).lab (D.inclusion_right e)).trans (rightEvent_lab m _)
  left_prec e f := (congrArg₂ (glueData A B m).prec (D.inclusion_left e) (D.inclusion_left f)).to_iff.trans
    (leftEvent_prec m hA _ _)
  right_prec e f := (congrArg₂ (glueData A B m).prec (D.inclusion_right e) (D.inclusion_right f)).to_iff.trans
    (rightEvent_prec m hB _ _)
  left_eord e f := (congrArg₂ (glueData A B m).eord (D.inclusion_left e) (D.inclusion_left f)).to_iff.trans
    (leftEvent_eord m hA _ _)
  right_eord e f := (congrArg₂ (glueData A B m).eord (D.inclusion_right e) (D.inclusion_right f)).to_iff.trans
    (rightEvent_eord m hA hB _ _)
  seam := D.seam
  overlap := overlap D
  cover := cover D
  cross := cross D
  source_len := congrArg Finset.card D.source_eq.symm
  target_len := congrArg Finset.card D.target_eq.symm
  source i := by
    apply (inclusion (glueData A B m) D.keepG).injective
    have hi := orderedSubset_enum_eq D.source_eq.symm i
      (Fin.cast (congrArg Finset.card D.source_eq.symm) i) rfl
    exact (D.inclusion_left _).trans ((congrArg (leftEvent m) (inclusion_source A D.keepA i)).trans
      ((congrArg (fun j => leftEvent m (A.src j)) hi).trans (inclusion_source (glueData A B m) D.keepG _).symm))
  target i := by
    apply (inclusion (glueData A B m) D.keepG).injective
    have hi := orderedSubset_enum_eq D.target_eq.symm i
      (Fin.cast (congrArg Finset.card D.target_eq.symm) i) rfl
    exact (D.inclusion_right _).trans ((congrArg (rightEvent m) (inclusion_target B D.keepB i)).trans
      ((congrArg (fun j => rightEvent m (B.tgt j)) hi).trans (inclusion_target (glueData A B m) D.keepG _).symm))

/-- Actual induced deletion commutes with genuine interface gluing whenever
the event predicates agree under the two canonical factor embeddings. -/
noncomputable def iso (hA : IsIntervalPom A) (hB : IsIntervalPom B) :
    PomsetIso (glueData D.leftData D.rightData D.glueMatch) D.gluedData :=
  (D.realization hA hB).iso (isIntervalPom A D.keepA hA) (isIntervalPom B D.keepB hB)
    (isIntervalPom (glueData A B m) D.keepG (glueData_isIntervalPom m hA hB))

end CounterFreeHDA.Deletion.Plan
