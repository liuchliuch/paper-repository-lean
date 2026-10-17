import CounterFreeHDA.CornerExtension
import CounterFreeHDA.FaceVariables

namespace CounterFreeHDA.Corners
universe u
variable {Lab : Type u} (P : PomsetData Lab) (α : Fin P.srcLen → Status)
    (β : Fin P.tgtLen → Status) (hc : Compatible P α β)

theorem source_iff (e : Fin (data P α β hc).n) :
    (data P α β hc).inSrc e ↔ ∃ i, P.src i = inclusion P α β hc e ∧ α i = Status.star := by
  classical
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨(source P α).orderEmbOfFin rfl j,(inclusion_source P α β hc j).symm,?_⟩
    exact (Finset.mem_filter.mp ((source P α).orderEmbOfFin_mem rfl j)).2
  · rintro ⟨i,hi,hα⟩
    have hm : i ∈ source P α := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hα⟩
    let j := (source P α).orderIsoOfFin rfl |>.symm ⟨i,hm⟩
    have hpos : (source P α).orderEmbOfFin rfl j = i :=
      congrArg Subtype.val ((source P α).orderIsoOfFin rfl |>.apply_symm_apply ⟨i,hm⟩)
    refine ⟨j,(inclusion P α β hc).injective ?_⟩
    exact (inclusion_source P α β hc j).trans ((congrArg P.src hpos).trans hi)

theorem target_iff (e : Fin (data P α β hc).n) :
    (data P α β hc).inTgt e ↔ ∃ i, P.tgt i = inclusion P α β hc e ∧ β i = Status.star := by
  classical
  constructor
  · rintro ⟨j,rfl⟩
    refine ⟨(target P β).orderEmbOfFin rfl j,(inclusion_target P α β hc j).symm,?_⟩
    exact (Finset.mem_filter.mp ((target P β).orderEmbOfFin_mem rfl j)).2
  · rintro ⟨i,hi,hβ⟩
    have hm : i ∈ target P β := Finset.mem_filter.mpr ⟨Finset.mem_univ i,hβ⟩
    let j := (target P β).orderIsoOfFin rfl |>.symm ⟨i,hm⟩
    have hpos : (target P β).orderEmbOfFin rfl j = i :=
      congrArg Subtype.val ((target P β).orderIsoOfFin rfl |>.apply_symm_apply ⟨i,hm⟩)
    refine ⟨j,(inclusion P α β hc).injective ?_⟩
    exact (inclusion_target P α β hc j).trans ((congrArg P.tgt hpos).trans hi)

end CounterFreeHDA.Corners

namespace CounterFreeHDA.Cubical.CornerFaces
universe u
variable {Lab : Type u} {k : ℕ} (P : PomsetData Lab) (hP : IsIntervalPom P)
    (hs : P.srcLen ≤ k) (ht : P.tgtLen ≤ k) {U V : Cube Lab k}
    (α : Face U (sourceCube P hs)) (β : Face V (targetCube P ht))
    (hc : Corners.Compatible P α.status β.status)

theorem source_type : (Corners.data P α.status β.status hc).srcType = cubeInterface U := by
  classical
  have hn : (Corners.source P α.status).card = U.dim := α.activePositions_card
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  refine ⟨hn,funext fun i => ?_⟩
  have hi := Corners.inclusion_source P α.status β.status hc i
  have hl : (Corners.data P α.status β.status hc).lab ((Corners.data P α.status β.status hc).src i) =
      P.lab (P.src ((Corners.source P α.status).orderEmbOfFin rfl i)) := congrArg P.lab hi
  exact hl.trans ((congrArg (P.lab ∘ P.src) (α.activePositions_orderEmb i)).trans
    (α.labels (α.position_spec (Fin.cast hn i))))

theorem target_type : (Corners.data P α.status β.status hc).tgtType = cubeInterface V := by
  classical
  have hn : (Corners.target P β.status).card = V.dim := β.activePositions_card
  apply Fin.sigma_eq_iff_eq_comp_cast.mpr
  refine ⟨hn,funext fun i => ?_⟩
  have hi := Corners.inclusion_target P α.status β.status hc i
  have hl : (Corners.data P α.status β.status hc).lab ((Corners.data P α.status β.status hc).tgt i) =
      P.lab (P.tgt ((Corners.target P β.status).orderEmbOfFin rfl i)) := congrArg P.lab hi
  exact hl.trans ((congrArg (P.lab ∘ P.tgt) (β.activePositions_orderEmb i)).trans
    (β.labels (β.position_spec (Fin.cast hn i))))

noncomputable def arrow : Arrow U V where
  pom := ⟨Corners.data P α.status β.status hc,Corners.isIntervalPom P α.status β.status hP hc⟩
  source := source_type P hs ht α β hc
  target := target_type P hs ht α β hc

end CounterFreeHDA.Cubical.CornerFaces
