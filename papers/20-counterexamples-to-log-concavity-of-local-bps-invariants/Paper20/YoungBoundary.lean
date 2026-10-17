import Paper20.YoungCorners

namespace Paper20.YoungCorners
open Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma removable_row_end (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    c.2+1=μ.rowLen c.1 := by
  have hlt := YoungDiagram.mem_iff_lt_rowLen.mp hc.1
  have hn : ¬c.2+1 < μ.rowLen c.1 := fun h => hc.2.2 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
  omega

lemma removable_row_drop (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    μ.rowLen (c.1+1) < μ.rowLen c.1 := by
  have he := removable_row_end μ c hc
  have hn : ¬c.2 < μ.rowLen (c.1+1) := fun h => hc.2.1 (YoungDiagram.mem_iff_lt_rowLen.mpr h)
  omega

/-- The unique addable corner in the top row. -/
def topCorner (μ : YoungDiagram) : ℕ × ℕ := (0,μ.rowLen 0)

lemma topCorner_addable (μ : YoungDiagram) : Addable μ (topCorner μ) := by
  refine ⟨?_,Or.inl rfl,?_⟩
  · exact fun h => (Nat.lt_irrefl _) (YoungDiagram.mem_iff_lt_rowLen.mp h)
  · by_cases hz : μ.rowLen 0=0
    · exact Or.inl hz
    · apply Or.inr
      exact YoungDiagram.mem_iff_lt_rowLen.mpr (by dsimp [topCorner]; omega)

lemma addable_top_iff (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Addable μ c) :
    c=topCorner μ ↔ c.1=0 := by
  constructor
  · intro h; exact congrArg Prod.fst h
  · intro h
    apply Prod.ext h
    simpa only [topCorner,h] using addable_row_end μ c hc

/-- The boundary step immediately below a genuine removable corner. -/
def downOuter (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ × ℕ :=
  (c.1+1,μ.rowLen (c.1+1))

lemma downOuter_addable (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    Addable μ (downOuter μ c) := by
  have hdrop := removable_row_drop μ c hc
  refine ⟨?_,Or.inr ?_,?_⟩
  · exact fun h => (Nat.lt_irrefl _) (YoungDiagram.mem_iff_lt_rowLen.mp h)
  · apply YoungDiagram.mem_iff_lt_rowLen.mpr
    simpa only [downOuter,Nat.add_sub_cancel] using hdrop
  · by_cases hz : μ.rowLen (c.1+1)=0
    · exact Or.inl hz
    · apply Or.inr
      exact YoungDiagram.mem_iff_lt_rowLen.mpr (by dsimp [downOuter]; omega)

/-- The inner corner immediately above a non-top addable corner. -/
def upInner (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ × ℕ :=
  (c.1-1,μ.rowLen (c.1-1)-1)

lemma upInner_removable (μ : YoungDiagram) (c : ℕ × ℕ)
    (hc : Addable μ c) (hpos : 0 < c.1) : Removable μ (upInner μ c) := by
  have hup : (c.1-1,c.2) ∈ μ := hc.2.1.resolve_left (by omega)
  have hlt := YoungDiagram.mem_iff_lt_rowLen.mp hup
  have hend := addable_row_end μ c hc
  have hp : 0 < μ.rowLen (c.1-1) := by omega
  refine ⟨?_,?_,?_⟩
  · exact YoungDiagram.mem_iff_lt_rowLen.mpr (by omega)
  · intro h
    have hm := YoungDiagram.mem_iff_lt_rowLen.mp h
    change μ.rowLen (c.1-1)-1 < μ.rowLen (c.1-1+1) at hm
    have hi : c.1-1+1=c.1 := by omega
    rw [hi] at hm
    omega
  · intro h
    have hm := YoungDiagram.mem_iff_lt_rowLen.mp h
    change μ.rowLen (c.1-1)-1+1 < μ.rowLen (c.1-1) at hm
    omega

lemma upInner_downOuter (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    upInner μ (downOuter μ c)=c := by
  have he := removable_row_end μ c hc
  apply Prod.ext
  · simp [upInner,downOuter]
  · dsimp [upInner,downOuter]
    omega

lemma downOuter_upInner (μ : YoungDiagram) (c : ℕ × ℕ)
    (hc : Addable μ c) (hpos : 0 < c.1) : downOuter μ (upInner μ c)=c := by
  have he := addable_row_end μ c hc
  have hi : c.1-1+1=c.1 := by omega
  apply Prod.ext
  · exact hi
  · dsimp [downOuter,upInner]
    rw [hi]
    exact he.symm

/-- Exact boundary counting in the actual Young lattice: there is one
more outer corner than inner corner, via the explicit boundary bijection. -/
theorem addable_card_eq_removable_add_one (μ : YoungDiagram) :
    (addableCells μ).card=(removableCells μ).card+1 := by
  have htop : topCorner μ ∈ addableCells μ := (mem_addableCells ..).2 (topCorner_addable μ)
  have he : (removableCells μ).card=((addableCells μ).erase (topCorner μ)).card := by
    apply Finset.card_bij (fun c _ => downOuter μ c)
    · intro c hc
      have hrem := (mem_removableCells μ c).1 hc
      rw [Finset.mem_erase,mem_addableCells]
      refine ⟨?_,downOuter_addable μ c hrem⟩
      intro h
      have hv := congrArg Prod.fst h
      dsimp [downOuter,topCorner] at hv
      omega
    · intro c hc d hd he
      have hv := congrArg Prod.fst he
      have hr := removable_row_end μ c ((mem_removableCells μ c).1 hc)
      have hs := removable_row_end μ d ((mem_removableCells μ d).1 hd)
      apply Prod.ext
      · dsimp [downOuter] at hv
        omega
      · have hi : c.1=d.1 := by dsimp [downOuter] at hv; omega
        rw [hi] at hr
        omega
    · intro c hc
      obtain ⟨hnt,hc⟩ := Finset.mem_erase.mp hc
      have ha := (mem_addableCells μ c).1 hc
      have hpos : 0 < c.1 := by
        have hn := (addable_top_iff μ c ha).not.mp hnt
        omega
      refine ⟨upInner μ c,(mem_removableCells ..).2 (upInner_removable μ c ha hpos),?_⟩
      exact downOuter_upInner μ c ha hpos
  rw [Finset.card_erase_of_mem htop] at he
  have hp : 0 < (addableCells μ).card := Finset.card_pos.mpr ⟨_,htop⟩
  omega

end
end Paper20.YoungCorners
