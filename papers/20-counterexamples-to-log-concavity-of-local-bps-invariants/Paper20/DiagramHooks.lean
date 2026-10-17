import Paper20.PartitionTranspose
import Paper20.Boxes

namespace Paper20
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem getD_gt_iff_lt_filter (ps : List ℕ) (hs : ps.Pairwise (· ≥ ·)) (i j : ℕ) :
    j < ps.getD i 0 ↔ i < (ps.filter (· > j)).length := by
  induction ps generalizing i with
  | nil => simp
  | cons b bs ih =>
    obtain ⟨hhead,htail⟩ := List.pairwise_cons.mp hs
    by_cases hb : j < b
    · cases i with
      | zero => simp [hb]
      | succ i => simpa [hb] using ih htail i
    · have hf : bs.filter (· > j) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        have hxle := hhead x hx
        have hn : ¬ x > j := by omega
        simpa using hn
      cases i with
      | zero => simp [hb,hf]
      | succ i => simpa [hb,hf] using ih htail i

namespace Part
variable {n : ℕ}

theorem diagram_rowLen (p : Part n) (i : ℕ) : p.diagram.rowLen i = p.parts.getD i 0 := by
  have h : ∀ j, j < p.diagram.rowLen i ↔ j < p.parts.getD i 0 := by
    intro j
    rw [← YoungDiagram.mem_iff_lt_rowLen]
    dsimp only [diagram]
    rw [YoungDiagram.mem_ofRowLens]
    by_cases hi : i < p.parts.length
    · rw [List.getD_eq_getElem _ _ hi]
      simp only [hi, exists_true_left]
    · rw [List.getD_eq_default _ _ (by omega)]
      simp only [hi, IsEmpty.exists_iff, Nat.not_lt_zero]
  have ha := h (p.diagram.rowLen i)
  have hb := h (p.parts.getD i 0)
  omega

theorem diagram_colLen (p : Part n) (j : ℕ) :
    p.diagram.colLen j = (p.parts.filter (· > j)).length := by
  have h : ∀ i, i < p.diagram.colLen j ↔ i < (p.parts.filter (· > j)).length := by
    intro i
    rw [← YoungDiagram.mem_iff_lt_colLen, YoungDiagram.mem_iff_lt_rowLen, diagram_rowLen]
    exact getD_gt_iff_lt_filter p.parts p.sorted i j
  have ha := h (p.diagram.colLen j)
  have hb := h ((p.parts.filter (· > j)).length)
  omega

end Part

def diagramHook (μ : YoungDiagram) (c : ℕ × ℕ) : ℕ :=
  μ.rowLen c.1-c.2+μ.colLen c.2-c.1-1

theorem diagramHook_transpose (μ : YoungDiagram) (c : ℕ × ℕ) (hc : c ∈ μ) :
    diagramHook μ.transpose c.swap = diagramHook μ c := by
  have hr := YoungDiagram.mem_iff_lt_rowLen.mp hc
  have hh := YoungDiagram.mem_iff_lt_colLen.mp hc
  simp only [diagramHook, Prod.fst_swap, Prod.snd_swap,
    YoungDiagram.rowLen_transpose, YoungDiagram.colLen_transpose]
  omega

theorem Part.hooks_eq_diagram (p : Part n) :
    hooksOf p.parts = (boxesOf p.parts).map (diagramHook p.diagram) := by
  rw [hooksOf_eq_boxes_map]
  apply List.map_congr_left
  intro c hc
  simp only [diagramHook, Part.diagram_rowLen, Part.diagram_colLen]

end Paper20
