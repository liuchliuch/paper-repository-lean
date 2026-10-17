import Paper20.PartitionHooks
import Mathlib.Combinatorics.Young.YoungDiagram

namespace Paper20
open Finset
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cellsOfRowLens_card (ps : List ℕ) :
    (YoungDiagram.cellsOfRowLens ps).card = ps.sum := by
  induction ps with
  | nil => rfl
  | cons a ps ih =>
    rw [YoungDiagram.cellsOfRowLens, Finset.card_union_of_disjoint]
    · simp [ih]
    · apply Finset.disjoint_left.mpr
      intro x hx hy
      obtain ⟨y, hy, he⟩ := Finset.mem_map.mp hy
      have hx0 : x.1=0 := by simpa using (Finset.mem_product.mp hx).1
      have he1 := congrArg Prod.fst he
      dsimp at he1
      omega

theorem rowLens_sum (μ : YoungDiagram) : μ.rowLens.sum = μ.cells.card := by
  have he : YoungDiagram.cellsOfRowLens μ.rowLens = μ.cells :=
    congrArg YoungDiagram.cells YoungDiagram.ofRowLens_to_rowLens_eq_self
  rw [← he, cellsOfRowLens_card]

namespace Part
variable {n : ℕ}

def diagram (p : Part n) : YoungDiagram := YoungDiagram.ofRowLens p.parts p.sorted

@[simp] theorem diagram_rowLens (p : Part n) : p.diagram.rowLens = p.parts :=
  YoungDiagram.rowLens_ofRowLens_eq_self p.pos

@[simp] theorem diagram_card (p : Part n) : p.diagram.cells.card = n := by
  change (YoungDiagram.cellsOfRowLens p.parts).card=n
  rw [cellsOfRowLens_card, p.sum_eq]

/-- Conjugation is the actual transposition of the corresponding Young
diagram, with its size and partition invariants derived. -/
def transpose (p : Part n) : Part n where
  parts := p.diagram.transpose.rowLens
  sorted := p.diagram.transpose.rowLens_sorted
  pos := p.diagram.transpose.pos_of_mem_rowLens
  sum_eq := by
    rw [rowLens_sum]
    simpa only [YoungDiagram.transpose, Equiv.finsetCongr_apply, Finset.card_map] using p.diagram_card

@[simp] theorem diagram_transpose (p : Part n) : p.transpose.diagram = p.diagram.transpose := by
  exact YoungDiagram.ofRowLens_to_rowLens_eq_self

@[simp] theorem transpose_parts (p : Part n) :
    p.transpose.parts = p.diagram.transpose.rowLens := rfl

@[ext] theorem ext_parts {p q : Part n} (h : p.parts = q.parts) : p=q := by
  cases p
  cases q
  cases h
  rfl

@[simp] theorem transpose_transpose (p : Part n) : p.transpose.transpose = p := by
  refine @ext_parts n p.transpose.transpose p ?_
  rw [transpose_parts, diagram_transpose, YoungDiagram.transpose_transpose, diagram_rowLens]

/-- Conjugation is a permutation of all partitions of the fixed size. -/
def transposeEquiv (n : ℕ) : Part n ≃ Part n where
  toFun := transpose
  invFun := transpose
  left_inv := transpose_transpose
  right_inv := transpose_transpose

end Part

end Paper20
