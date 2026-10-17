import Paper20.StandardContents

namespace Paper20.YoungShapes
open Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- Distinct addable corners of an actual Young diagram are incomparable. -/
theorem addable_not_le (μ : YoungDiagram) (c d : ℕ × ℕ)
    (hc : Addable μ c) (hd : Addable μ d) (hne : c≠d) : ¬c≤d := by
  intro hle
  exact hc.1 (addable_lower μ d hd c hle hne)

/-- The actual content distinguishes every pair of actual addable
corners. It therefore determines a one-box extension of a fixed shape. -/
theorem addable_content_injective (μ : YoungDiagram) (c d : ℕ × ℕ)
    (hc : Addable μ c) (hd : Addable μ d) (he : cellContent c=cellContent d) : c=d := by
  by_contra hn
  have hcd := addable_not_le μ c d hc hd hn
  have hdc := addable_not_le μ d c hd hc (fun h => hn h.symm)
  dsimp only [cellContent] at he
  by_cases hr : c.1≤d.1
  · exact hcd ⟨hr,by omega⟩
  · exact hdc ⟨by omega,by omega⟩

/-- Actual incomparable cell positions have content differences outside
both forbidden row/column boundary values. -/
theorem incomparable_content_gap (c d : ℕ × ℕ) (hcd : ¬c≤d) (hdc : ¬d≤c) :
    2≤cellContent c-cellContent d ∨ 2≤cellContent d-cellContent c := by
  dsimp only [cellContent]
  have hn1 : ¬(c.1≤d.1 ∧ c.2≤d.2) := hcd
  have hn2 : ¬(d.1≤c.1 ∧ d.2≤c.2) := hdc
  omega

end
end Paper20.YoungShapes
