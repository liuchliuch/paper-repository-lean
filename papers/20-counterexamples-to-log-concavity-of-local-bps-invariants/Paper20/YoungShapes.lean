import Paper20.PartitionFinite

namespace Paper20.YoungShapes
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- All actual Young diagrams of exactly the specified cardinal. -/
abbrev Shape (n : ℕ) := {μ : YoungDiagram // μ.cells.card=n}

/-- The genuine finite Young-diagram level is exactly the existing
complete positive-partition type, rather than an independently chosen
finite list of shapes. -/
def shapeEquivPart (n : ℕ) : Shape n ≃ Part n where
  toFun μ :=
    { parts := μ.val.rowLens
      sorted := μ.val.rowLens_sorted
      pos := μ.val.pos_of_mem_rowLens
      sum_eq := (rowLens_sum μ.val).trans μ.property }
  invFun p := ⟨p.diagram,p.diagram_card⟩
  left_inv μ := by
    apply Subtype.ext
    exact YoungDiagram.ofRowLens_to_rowLens_eq_self
  right_inv p := by
    apply Part.ext_parts
    exact p.diagram_rowLens

instance shapeFintype (n : ℕ) : Fintype (Shape n) :=
  Fintype.ofEquiv (Part n) (shapeEquivPart n).symm

/-- Every actual shape is counted precisely once in the common complete
partition enumeration. -/
theorem sum_shapes {M : Type*} [AddCommMonoid M] (n : ℕ) (f : List ℕ → M) :
    (∑ μ : Shape n, f μ.val.rowLens)=((partitionsOf n).map f).sum := by
  classical
  rw [← Part.sum_over_partitions n f]
  exact Fintype.sum_equiv (shapeEquivPart n) _ _ (by intro μ; rfl)

instance shapeZeroUnique : Unique (Shape 0) where
  default := ⟨⊥,by simp⟩
  uniq μ := by
    apply Subtype.ext
    apply YoungDiagram.ext
    exact Finset.card_eq_zero.mp μ.property

/-- The unique initial vertex is the actual empty diagram. -/
theorem shape_zero_card : Fintype.card (Shape 0)=1 := Fintype.card_unique

end
end Paper20.YoungShapes
