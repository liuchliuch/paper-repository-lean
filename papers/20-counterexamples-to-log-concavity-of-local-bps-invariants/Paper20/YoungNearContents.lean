import Paper20.StandardContents

namespace Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

lemma index_between_cells {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (c : Cells μ.val)
    (hac : position t i<c.val) (hcb : c.val<position t j) :
    i < (positionEquiv t).symm c ∧ (positionEquiv t).symm c < j := by
  let k := (positionEquiv t).symm c
  have hk := position_filling t c
  constructor
  · apply index_lt_of_position_le t i k
    · rw [hk]; exact hac.le
    · intro he
      have hp := congrArg (position t) he
      rw [hk] at hp
      exact hac.ne hp
  · apply index_lt_of_position_le t k j
    · rw [hk]; exact hcb.le
    · intro he
      have hp := congrArg (position t) he
      rw [hk] at hp
      exact hcb.ne hp

/-- Equal diagonal contents require a gap of at least three labels:
there are two distinct actual intermediate cells, one to the right and
one below the first cell. -/
theorem near_content_ne {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (hij : i < j) (hgap : j.val ≤ i.val+2) : pathContent t i≠pathContent t j := by
  intro he
  let a := position t i
  let b := position t j
  have hc : (a.2:ℤ)-(a.1:ℤ)=(b.2:ℤ)-(b.1:ℤ) := he
  have hreverse : ¬b≤a := position_not_reverse t i j hij
  have hr : a.1 < b.1 := by
    by_contra hn
    exact hreverse ⟨by omega,by omega⟩
  have hcol : a.2 < b.2 := by omega
  have hcm : (a.1,a.2+1) ∈ μ.val :=
    μ.val.isLowerSet (show (a.1,a.2+1)≤b from ⟨by omega,by omega⟩) (position_mem t j)
  have hdm : (a.1+1,a.2) ∈ μ.val :=
    μ.val.isLowerSet (show (a.1+1,a.2)≤b from ⟨by omega,by omega⟩) (position_mem t j)
  let c : Cells μ.val := ⟨(a.1,a.2+1),hcm⟩
  let d : Cells μ.val := ⟨(a.1+1,a.2),hdm⟩
  have hca : a < c.val := by
    change a < (a.1,a.2+1)
    apply lt_iff_le_not_ge.mpr
    refine ⟨⟨le_rfl,Nat.le_succ _⟩,?_⟩
    intro h; have := h.2; omega
  have hcb : c.val < b := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨⟨by change a.1≤b.1; omega,by change a.2+1≤b.2; omega⟩,?_⟩
    intro h; have hh := h.1; change b.1≤a.1 at hh; omega
  have hda : a < d.val := by
    change a < (a.1+1,a.2)
    apply lt_iff_le_not_ge.mpr
    refine ⟨⟨Nat.le_succ _,le_rfl⟩,?_⟩
    intro h; have := h.1; omega
  have hdb : d.val < b := by
    apply lt_iff_le_not_ge.mpr
    refine ⟨⟨by change a.1+1≤b.1; omega,by change a.2≤b.2; omega⟩,?_⟩
    intro h; have hh := h.2; change b.2≤a.2 at hh; omega
  have hcidx := index_between_cells t i j c hca hcb
  have hdidx := index_between_cells t i j d hda hdb
  have hc1 : i.val < ((positionEquiv t).symm c).val := hcidx.1
  have hc2 : ((positionEquiv t).symm c).val < j.val := hcidx.2
  have hd1 : i.val < ((positionEquiv t).symm d).val := hdidx.1
  have hd2 : ((positionEquiv t).symm d).val < j.val := hdidx.2
  have hidx : (positionEquiv t).symm c=(positionEquiv t).symm d := Fin.ext (by omega)
  have hcd := (positionEquiv t).symm.injective hidx
  have hrow := congrArg (fun e : Cells μ.val => e.val.1) hcd
  change a.1=a.1+1 at hrow
  omega

/-- Every three consecutive standard-tableau eigenvalue contents are
pairwise distinct, including the first and third labels. -/
theorem filling_content_triple_ne {n : ℕ} {μ : Shape n} (t : StandardFilling μ)
    (i j k : Fin n) (hij : j.val=i.val+1) (hjk : k.val=j.val+1) :
    fillingContent t i≠fillingContent t j ∧
      fillingContent t j≠fillingContent t k ∧ fillingContent t i≠fillingContent t k := by
  refine ⟨filling_adjacent_content_ne t i j hij,filling_adjacent_content_ne t j k hjk,?_⟩
  have he := near_content_ne (fillingPath n μ t) i k
    (by change i.val < k.val; omega) (by omega)
  simpa only [fillingPath_content] using he

end
end Paper20.YoungShapes
