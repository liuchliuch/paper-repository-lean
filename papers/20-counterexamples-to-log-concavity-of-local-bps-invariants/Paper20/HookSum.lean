import Paper20.PartitionShift

namespace Paper20
open Finset
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def boxArm (ps : List ℕ) (c : ℕ × ℕ) : ℕ := ps.getD c.1 0-1-c.2

theorem boxes_sum_arms (ps : List ℕ) :
    ((boxesOf ps).map (boxArm ps)).sum = ((boxesOf ps).map Prod.snd).sum := by
  unfold boxesOf
  rw [List.map_flatMap, List.map_flatMap, sum_flatMap_nat, sum_flatMap_nat]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p hp
  rcases p with ⟨a,i⟩
  dsimp only
  have he : ps.getD i 0 = a := by
    rw [List.getD_eq_getD_getElem?, List.mk_mem_zipIdx_iff_getElem?.mp hp]
    rfl
  rw [List.map_map, List.map_map]
  simp only [Function.comp_def, boxArm, he]
  rw [sum_map_range_nat, sum_map_range_nat]
  exact Finset.sum_range_reflect (fun j => j) a

theorem boxesOf_length (ps : List ℕ) : (boxesOf ps).length=ps.sum := by
  rw [← List.toFinset_card_of_nodup (boxesOf_nodup ps), boxesOf_toFinset, cellsOfRowLens_card]

namespace Part
variable {n : ℕ}

theorem sum_arms (p : Part n) :
    ((boxesOf p.parts).map (boxArm p.parts)).sum = nuOf p.transpose.parts := by
  rw [boxes_sum_arms, nuOf_transpose_boxes]

theorem sum_legs (p : Part n) :
    ((boxesOf p.parts).map (fun c => p.diagram.colLen c.2-1-c.1)).sum = nuOf p.parts := by
  have he := (p.boxes_transpose_perm.map (boxArm p.transpose.parts)).sum_eq
  have ha := p.transpose.sum_arms
  rw [transpose_transpose] at ha
  rw [ha, List.map_map] at he
  symm at he
  convert he using 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro c hc
  simp only [Function.comp_def, boxArm, Prod.fst_swap, Prod.snd_swap,
    ← diagram_rowLen, diagram_transpose, YoungDiagram.rowLen_transpose]

/-- The hook sum identity in the proof of (18), for the actual executable
hook, size and nu definitions. -/
theorem hook_sum (p : Part n) :
    (hooksOf p.parts).sum = n+nuOf p.parts+nuOf p.transpose.parts := by
  rw [p.hooks_eq_diagram]
  have he : ((boxesOf p.parts).map (diagramHook p.diagram)).sum =
      ((boxesOf p.parts).map (fun c => 1+boxArm p.parts c+
        (p.diagram.colLen c.2-1-c.1))).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro c hc
    have hd : c ∈ p.diagram := by
      change c ∈ YoungDiagram.ofRowLens p.parts p.sorted
      exact YoungDiagram.mem_ofRowLens.mpr ((mem_boxesOf p.parts c.1 c.2).mp hc)
    have hr := YoungDiagram.mem_iff_lt_rowLen.mp hd
    have hl := YoungDiagram.mem_iff_lt_colLen.mp hd
    simp only [diagramHook, boxArm, p.diagram_rowLen] at hr ⊢
    omega
  rw [he]
  have hs : ∀ xs : List (ℕ × ℕ),
      (xs.map (fun c => 1+boxArm p.parts c+(p.diagram.colLen c.2-1-c.1))).sum =
        xs.length+(xs.map (boxArm p.parts)).sum+
          (xs.map (fun c => p.diagram.colLen c.2-1-c.1)).sum := by
    intro xs
    induction xs with
    | nil => rfl
    | cons c xs ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  rw [hs, boxesOf_length, p.sum_eq, sum_arms, sum_legs]
  omega

end Part
end Paper20
