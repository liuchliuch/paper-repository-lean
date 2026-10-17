import Paper20.PaddedBranching
import Paper20.YoungShapes
import Paper20.YoungCovers

namespace Paper20.YoungShapes
open Matrix Finset Paper20.YoungCorners Paper20.HookDeterminant
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- The actual executable hook quotient, applied to the complete row
partition of an actual Young diagram. -/
def dimension (μ : YoungDiagram) : ℕ := dimOf μ.cells.card μ.rowLens

lemma dimension_det (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m) :
    (dimension μ:ℚ)=(orientation m:ℚ)*(μ.cells.card.factorial:ℚ)*
      (factorialMatrix (paddedBeta μ m) (fun j => j.val)).det := by
  let p := shapeEquivPart μ.cells.card ⟨μ,rfl⟩
  have hp : p.diagram=μ := YoungDiagram.ofRowLens_to_rowLens_eq_self
  have he := padded_dim_det p m (by rw [hp]; exact hm)
  simpa only [hp] using he

/-- Genuine removable rows and genuine removable cells are in bijection,
including when the partition has zero padded rows. -/
def rowCornerEquiv (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m) :
    {i : Fin m // Removable μ (i.val,μ.rowLen i.val-1)} ≃
      {c : ℕ × ℕ // c ∈ removableCells μ} where
  toFun i := ⟨(i.val.val,μ.rowLen i.val.val-1),(mem_removableCells ..).mpr i.property⟩
  invFun c :=
    let hr := (mem_removableCells μ c.val).mp c.property
    ⟨⟨c.val.1,by have := corner_row_bound μ c.val hr; omega⟩,by
      have he := removable_row_end μ c.val hr
      have hc : (c.val.1,μ.rowLen c.val.1-1)=c.val := Prod.ext rfl (by omega)
      simpa only [hc] using hr⟩
  left_inv i := Subtype.ext (Fin.ext rfl)
  right_inv c := by
    apply Subtype.ext
    have he := removable_row_end μ c.val ((mem_removableCells ..).mp c.property)
    exact Prod.ext rfl (by dsimp; omega)

def rowLowerEquiv (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m) :
    {i : Fin m // Removable μ (i.val,μ.rowLen i.val-1)} ≃
      {κ : YoungDiagram // Covers κ μ} :=
  (rowCornerEquiv μ m hm).trans (lowerCoverEquiv μ).symm

/-- The exact natural hook quotient obeys single-box branching on the
actual Young lattice. The proof uses the factorial determinant recurrence
and the actual corner bijection, with no representation or tableau premise. -/
theorem dimension_branching (μ : YoungDiagram) (hμ : 0<μ.cells.card) :
    (∑ κ : {κ : YoungDiagram // Covers κ μ}, dimension κ.val)=dimension μ := by
  let m := μ.colLen 0
  let b := paddedBeta μ m
  let f : Fin m → ℚ := fun i =>
    ((factorialMatrix b (fun j => j.val)).updateRow i
      (lowerFactorialRow b (fun j => j.val) i)).det
  have hs : (∑ i : {i : Fin m // Removable μ (i.val,μ.rowLen i.val-1)}, f i.val)=
      (μ.cells.card:ℚ)*(factorialMatrix b (fun j => j.val)).det := by
    have he := Finset.sum_congr_set
      (s:={i : Fin m | Removable μ (i.val,μ.rowLen i.val-1)}) f
      (fun i => f i.val) (by intro i hi; rfl)
      (by intro i hi; exact invalid_lower_det μ m le_rfl i hi)
    exact he.symm.trans (factorial_det_branching b (fun j => j.val) (paddedBeta_sum μ m le_rfl))
  have hfactor : μ.cells.card.factorial=μ.cells.card*(μ.cells.card-1).factorial := by
    have he : μ.cells.card=(μ.cells.card-1)+1 := by omega
    have hf := Nat.factorial_succ (μ.cells.card-1)
    rw [← he] at hf
    exact hf
  have hq : (dimension μ:ℚ)=
      ∑ κ : {κ : YoungDiagram // Covers κ μ}, (dimension κ.val:ℚ) := by
    calc
      (dimension μ:ℚ) = (orientation m:ℚ)*(μ.cells.card.factorial:ℚ)*
          (factorialMatrix b (fun j => j.val)).det := dimension_det μ m le_rfl
      _ = (orientation m:ℚ)*((μ.cells.card-1).factorial:ℚ)*
          ((μ.cells.card:ℚ)*(factorialMatrix b (fun j => j.val)).det) := by
        rw [hfactor,Nat.cast_mul]
        ring
      _ = (orientation m:ℚ)*((μ.cells.card-1).factorial:ℚ)*
          (∑ i : {i : Fin m // Removable μ (i.val,μ.rowLen i.val-1)}, f i.val) := by rw [hs]
      _ = ∑ i : {i : Fin m // Removable μ (i.val,μ.rowLen i.val-1)},
          (dimension (erase μ (i.val.val,μ.rowLen i.val.val-1) i.property):ℚ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i hi
        rw [dimension_det _ m (erase_height_le μ _ i.property),erase_card]
        dsimp only [f,b]
        rw [valid_lower_det μ m le_rfl i.val i.property]
      _ = _ := Fintype.sum_equiv (rowLowerEquiv μ m le_rfl) _ _ (by intro i; rfl)
  exact_mod_cast hq.symm

end
end Paper20.YoungShapes
