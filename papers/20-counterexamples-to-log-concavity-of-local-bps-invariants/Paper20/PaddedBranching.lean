import Paper20.PaddedDimensionDet
import Paper20.YoungRowErase

namespace Paper20.HookDeterminant
open Matrix Finset Paper20.HookBeta Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

lemma paddedBeta_sum (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m) :
    (∑ i : Fin m, paddedBeta μ m i)=μ.cells.card+∑ i : Fin m, i.val := by
  obtain ⟨t,rfl⟩ := Nat.exists_eq_add_of_le hm
  induction t with
  | zero =>
    simpa only [Nat.add_zero,paddedBeta,betaVector,beta] using betaVector_sum μ
  | succ t ih =>
    have he : μ.colLen 0+(t+1)=μ.colLen 0+t+1 := by omega
    rw [he,paddedBeta_grow μ _ (by omega)]
    simp only [Fin.sum_univ_castSucc,Fin.snoc_castSucc,Fin.snoc_last,
      Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
      smul_eq_mul,mul_one,Fin.coe_castSucc,Fin.val_last,add_zero]
    rw [ih (by omega)]
    omega

lemma removable_row_iff (μ : YoungDiagram) (i : ℕ) :
    Removable μ (i,μ.rowLen i-1) ↔
      0<μ.rowLen i ∧ μ.rowLen (i+1)<μ.rowLen i := by
  unfold Removable
  simp only [YoungDiagram.mem_iff_lt_rowLen]
  omega

/-- Every invalid row lowering in the actual padded hook determinant
vanishes: it either produces a zero row or repeats the following row. -/
theorem invalid_lower_det (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m)
    (i : Fin m) (hi : ¬Removable μ (i.val,μ.rowLen i.val-1)) :
    ((factorialMatrix (paddedBeta μ m) (fun j => j.val)).updateRow i
      (lowerFactorialRow (paddedBeta μ m) (fun j => j.val) i)).det=0 := by
  let b := paddedBeta μ m
  by_cases hz : b i=0
  · apply Matrix.det_eq_zero_of_row_eq_zero i
    intro j
    simp only [Matrix.updateRow_self]
    change (if j.val+1≤b i then 1/((b i-j.val-1).factorial:ℚ) else 0)=0
    rw [hz,if_neg (by omega : ¬(j.val+1≤0))]
  · have hbpos : 0<b i := Nat.pos_of_ne_zero hz
    by_cases hn : i.val + 1 < m
    · let j : Fin m := ⟨i.val+1,hn⟩
      have hji : j≠i := by intro h; have := congrArg Fin.val h; dsimp [j] at this; omega
      have he : μ.rowLen (i.val+1)=μ.rowLen i.val := by
        have ha := μ.rowLen_anti i.val (i.val+1) (by omega)
        rw [removable_row_iff] at hi
        omega
      have hb : b i-1=b j := by
        have hilt := i.isLt
        dsimp only [b,paddedBeta,j]
        rw [he]
        omega
      rw [← factorialMatrix_lower_update b _ i hbpos]
      apply Matrix.det_zero_of_row_eq hji.symm
      funext k
      simp only [factorialMatrix,Function.update_self,Function.update_of_ne hji,hb]
    · have he : i.val+1=m := by have := i.isLt; omega
      have hnz : μ.rowLen (i.val+1)=0 := by rw [he]; exact rowLen_zero_of_height_le μ m hm
      have hr : μ.rowLen i.val=0 := by rw [removable_row_iff] at hi; omega
      have hb : b i=0 := by dsimp only [b,paddedBeta]; rw [hr]; omega
      exact (hz hb).elim

/-- On every genuine removable row, the actual lowered determinant is
exactly the padded determinant of the actual erased Young diagram. -/
theorem valid_lower_det (μ : YoungDiagram) (m : ℕ) (hm : μ.colLen 0 ≤ m)
    (i : Fin m) (hi : Removable μ (i.val,μ.rowLen i.val-1)) :
    ((factorialMatrix (paddedBeta μ m) (fun j => j.val)).updateRow i
      (lowerFactorialRow (paddedBeta μ m) (fun j => j.val) i)).det=
    (factorialMatrix (paddedBeta (erase μ (i.val,μ.rowLen i.val-1) hi) m)
      (fun j => j.val)).det := by
  have hp : 0<paddedBeta μ m i := by
    have hr := (removable_row_iff μ i.val).mp hi
    have hilt := i.isLt
    dsimp only [paddedBeta]
    omega
  rw [← factorialMatrix_lower_update _ _ i hp,erase_paddedBeta μ _ hi m hm]

end
end Paper20.HookDeterminant
