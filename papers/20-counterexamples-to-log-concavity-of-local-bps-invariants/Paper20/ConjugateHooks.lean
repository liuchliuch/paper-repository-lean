import Paper20.DiagramHooks
import Paper20.RSeriesSemantics

namespace Paper20.Part
noncomputable section
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
variable {n : ℕ}

theorem boxes_to_diagram (p : Part n) :
    (boxesOf p.parts).toFinset = p.diagram.cells := boxesOf_toFinset p.parts

theorem boxes_transpose_perm (p : Part n) :
    (boxesOf p.transpose.parts).Perm ((boxesOf p.parts).map Prod.swap) := by
  apply (List.perm_ext_iff_of_nodup (boxesOf_nodup _)
    ((boxesOf_nodup _).map Prod.swap_injective)).2
  intro c
  have hm : c ∈ (boxesOf p.parts).map Prod.swap ↔ c.swap ∈ boxesOf p.parts := by
    constructor
    · intro hc
      obtain ⟨x,hx,he⟩ := List.mem_map.mp hc
      have hx' : x ∈ boxesOf p.parts := hx
      rw [← he]
      simpa using hx'
    · intro hc
      exact List.mem_map.mpr ⟨c.swap,hc,Prod.swap_swap c⟩
  rw [hm]
  simp only [← List.mem_toFinset, boxes_to_diagram]
  simp only [YoungDiagram.mem_cells, diagram_transpose, YoungDiagram.mem_transpose]

/-- Conjugation preserves the complete hook multiset, not only its product. -/
theorem hooks_transpose_perm (p : Part n) :
    (hooksOf p.transpose.parts).Perm (hooksOf p.parts) := by
  rw [p.transpose.hooks_eq_diagram, p.hooks_eq_diagram]
  have hp := p.boxes_transpose_perm.map (diagramHook p.transpose.diagram)
  have he : ((boxesOf p.parts).map Prod.swap).map (diagramHook p.transpose.diagram) =
      (boxesOf p.parts).map (diagramHook p.diagram) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro c hc
    dsimp only [Function.comp_apply]
    rw [diagram_transpose]
    apply diagramHook_transpose
    change c ∈ YoungDiagram.ofRowLens p.parts p.sorted
    exact YoungDiagram.mem_ofRowLens.mpr ((mem_boxesOf p.parts c.1 c.2).mp hc)
  rw [he] at hp
  exact hp

@[simp] theorem hook_product_transpose (p : Part n) :
    (hooksOf p.transpose.parts).prod = (hooksOf p.parts).prod := p.hooks_transpose_perm.prod_eq

@[simp] theorem dimOf_transpose (p : Part n) : dimOf n p.transpose.parts = dimOf n p.parts := by
  unfold dimOf
  rw [hook_product_transpose]

@[simp] theorem partsEvenHooks_transpose (p : Part n) :
    partsEvenHooks p.transpose.parts = partsEvenHooks p.parts := by
  unfold partsEvenHooks
  rw [partsHooks_eq_hooksOf, partsHooks_eq_hooksOf]
  exact p.hooks_transpose_perm.countP_eq _

lemma Rproduct_of_perm {xs ys : List ℕ} (hx : xs.Perm ys) (e f : ℕ) (he : e=f) :
    LogSeries.Rproduct xs e = LogSeries.Rproduct ys f := by
  unfold LogSeries.Rproduct
  rw [he]
  exact congrArg (fun z => LogSeries.affineBase⁻¹^(f/2)*z)
    (((hx.map Dpoly).map LogSeries.normalizedFactor).prod_eq)

/-- The complete genuine R product is invariant under partition conjugation. -/
theorem Rproduct_transpose (p : Part n) :
    LogSeries.Rproduct (hooksOf p.transpose.parts) (partsEvenHooks p.transpose.parts) =
      LogSeries.Rproduct (hooksOf p.parts) (partsEvenHooks p.parts) := by
  exact Rproduct_of_perm p.hooks_transpose_perm _ _ p.partsEvenHooks_transpose

end
end Paper20.Part
