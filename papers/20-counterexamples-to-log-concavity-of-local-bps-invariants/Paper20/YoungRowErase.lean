import Paper20.YoungBoundary
import Paper20.FactorialBranching
import Paper20.PaddedHookVandermonde

namespace Paper20.YoungCorners
open Finset Paper20.HookDeterminant
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

/-- Erasing an actual inner corner lowers exactly its row by one. -/
theorem erase_rowLen (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) (k : ℕ) :
    (erase μ c hc).rowLen k=if k=c.1 then μ.rowLen k-1 else μ.rowLen k := by
  have he (j : ℕ) : j < (erase μ c hc).rowLen k ↔
      j < if k=c.1 then μ.rowLen k-1 else μ.rowLen k := by
    rw [← YoungDiagram.mem_iff_lt_rowLen (μ:=erase μ c hc),erase_mem]
    rw [YoungDiagram.mem_iff_lt_rowLen (μ:=μ)]
    by_cases hk : k=c.1
    · subst k
      have hend := removable_row_end μ c hc
      rw [if_pos rfl]
      constructor
      · rintro ⟨hne,hlt⟩
        have hjne : j≠c.2 := fun h => hne (Prod.ext rfl h)
        omega
      · intro hlt
        refine ⟨?_,by omega⟩
        intro h
        have hv := congrArg Prod.snd h
        omega
    · rw [if_neg hk]
      constructor
      · exact And.right
      · intro hlt
        refine ⟨?_,hlt⟩
        intro h
        exact hk (congrArg Prod.fst h)
  have h1 := he ((erase μ c hc).rowLen k)
  have h2 := he (if k=c.1 then μ.rowLen k-1 else μ.rowLen k)
  omega

lemma corner_row_bound (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) : c.1 < μ.colLen 0 := by
  have hi := YoungDiagram.mem_iff_lt_colLen.mp hc.1
  have hm := μ.colLen_anti 0 c.2 (Nat.zero_le _)
  omega

lemma erase_height_le (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c) :
    (erase μ c hc).colLen 0 ≤ μ.colLen 0 := by
  by_contra hn
  have hm : (μ.colLen 0,0) ∈ erase μ c hc :=
    YoungDiagram.mem_iff_lt_colLen.mpr (by omega)
  have ho : (μ.colLen 0,0) ∈ μ := ((erase_mem μ c hc _).1 hm).2
  have hi := YoungDiagram.mem_iff_lt_colLen.mp ho
  omega

/-- The actual fixed-bound beta vector changes in precisely one entry. -/
theorem erase_paddedBeta (μ : YoungDiagram) (c : ℕ × ℕ) (hc : Removable μ c)
    (m : ℕ) (hm : μ.colLen 0 ≤ m) :
    paddedBeta (erase μ c hc) m=
      Function.update (paddedBeta μ m) (⟨c.1,by have := corner_row_bound μ c hc; omega⟩:Fin m)
        (paddedBeta μ m ⟨c.1,by have := corner_row_bound μ c hc; omega⟩-1) := by
  funext j
  have hj := j.isLt
  have hp : 0 < μ.rowLen c.1 := by
    have hi := YoungDiagram.mem_iff_lt_rowLen.mp hc.1
    omega
  by_cases he : j.val=c.1
  · have hjc : j=(⟨c.1,by have := corner_row_bound μ c hc; omega⟩:Fin m) := Fin.ext he
    rw [Function.update_apply,if_pos hjc]
    simp only [paddedBeta,erase_rowLen,Fin.val_mk,if_pos he,he,if_true]
    omega
  · have hjc : j≠(⟨c.1,by have := corner_row_bound μ c hc; omega⟩:Fin m) := by
      intro h
      exact he (congrArg Fin.val h)
    rw [Function.update_apply,if_neg hjc]
    simp only [paddedBeta,erase_rowLen,if_neg he]

end
end Paper20.YoungCorners

namespace Paper20.HookDeterminant
open Matrix
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

/-- Lowering a positive beta entry is exactly the determinant's genuine
lower-factorial row operation, including every invalid-index zero. -/
theorem factorialMatrix_lower_update {m : ℕ} (b d : Fin m → ℕ) (i : Fin m) (hi : 0 < b i) :
    factorialMatrix (Function.update b i (b i-1)) d=
      (factorialMatrix b d).updateRow i (lowerFactorialRow b d i) := by
  classical
  apply Matrix.ext
  intro j k
  by_cases hj : j=i
  · subst j
    simp only [factorialMatrix,Function.update_self,Matrix.updateRow_self,lowerFactorialRow]
    have he : d k ≤ b i-1 ↔ d k+1 ≤ b i := by omega
    have hf : b i-1-d k=b i-d k-1 := by omega
    by_cases hd : d k+1 ≤ b i
    · rw [if_pos (he.mpr hd),if_pos hd,hf]
    · rw [if_neg (fun h => hd (he.mp h)),if_neg hd]
  · simp only [factorialMatrix,Function.update_of_ne hj,Matrix.updateRow_ne hj]

end
end Paper20.HookDeterminant
