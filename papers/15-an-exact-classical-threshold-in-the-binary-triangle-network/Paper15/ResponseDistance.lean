import Paper15.ResponseCube

noncomputable section
namespace Paper15
open Finset BigOperators

def tableDist (T U : RespTable) : Nat := ∑i,∑j,if T i j=U i j then 0 else 1
lemma tableDist_reindex (T U : RespTable) (σ τ : Equiv.Perm (Fin 3)) :
    (∑i,∑j,if T (σ i) (τ j)=U (σ i) (τ j) then (0:Nat) else 1) = tableDist T U := by
  calc
    _ = ∑i,∑j,if T (σ i) j=U (σ i) j then (0:Nat) else 1 :=
      sum_congr rfl (fun i _ => Equiv.sum_comp τ _)
    _ = _ := Equiv.sum_comp σ (fun i => ∑j,if T i j=U i j then (0:Nat) else 1)
lemma tableDist_swap (T U : RespTable) : tableDist T.swap U.swap=tableDist T U := by
  exact sum_comm
lemma tableDist_flip (T U : RespTable) : tableDist T.flip U.flip=tableDist T U := by
  simp only [tableDist,RespTable.flip,neg_inj]

lemma bits_eq_iff (T U : DetTriangle) (p : Fin 27) :
    T.bits p=U.bits p ↔ T.signAtPos p.val=U.signAtPos p.val := by
  constructor
  · intro h
    simpa only [DetTriangle.signOfBit_bits] using congrArg signOfBit h
  · intro h
    apply signOfBit_injective
    simpa only [DetTriangle.signOfBit_bits] using h

set_option maxRecDepth 10000 in
lemma responseDist_entries (T U : DetTriangle) :
    responseDist T U=tableDist T.A U.A+tableDist T.B U.B+tableDist T.C U.C := by
  unfold responseDist
  simp_rw [bits_eq_iff]
  simp [DetTriangle.signAtPos,tableDist,Fin.sum_univ_succ]
  omega

lemma responseDist_valueReindex (T U : DetTriangle) (σ τ υ : Equiv.Perm (Fin 3)) :
    responseDist (valueReindex σ τ υ T) (valueReindex σ τ υ U)=responseDist T U := by
  simp only [responseDist_entries,valueReindex,tableDist]
  rw [tableDist_reindex,tableDist_reindex,tableDist_reindex]
  rfl

lemma responseDist_swapXY (T U : DetTriangle) : responseDist (swapXY T) (swapXY U)=responseDist T U := by
  simp only [responseDist_entries,swapXY,tableDist,RespTable.swap]
  have h (f : Fin 3 → Fin 3 → Nat) : (∑i,∑j,f j i)=∑i,∑j,f i j := sum_comm
  have hA := h (fun i j => if T.A i j=U.A i j then 0 else 1)
  have hB := h (fun i j => if T.B i j=U.B i j then 0 else 1)
  have hC := h (fun i j => if T.C i j=U.C i j then 0 else 1)
  rw [hA,hB,hC]
  omega
lemma responseDist_swapYZ (T U : DetTriangle) : responseDist (swapYZ T) (swapYZ U)=responseDist T U := by
  simp only [responseDist_entries,swapYZ,tableDist,RespTable.swap]
  have h (f : Fin 3 → Fin 3 → Nat) : (∑i,∑j,f j i)=∑i,∑j,f i j := sum_comm
  have hA := h (fun i j => if T.A i j=U.A i j then 0 else 1)
  have hB := h (fun i j => if T.B i j=U.B i j then 0 else 1)
  have hC := h (fun i j => if T.C i j=U.C i j then 0 else 1)
  rw [hA,hB,hC]
  omega
lemma responseDist_swapXZ (T U : DetTriangle) : responseDist (swapXZ T) (swapXZ U)=responseDist T U := by
  simp only [responseDist_entries,swapXZ,tableDist,RespTable.swap]
  have h (f : Fin 3 → Fin 3 → Nat) : (∑i,∑j,f j i)=∑i,∑j,f i j := sum_comm
  have hA := h (fun i j => if T.A i j=U.A i j then 0 else 1)
  have hB := h (fun i j => if T.B i j=U.B i j then 0 else 1)
  have hC := h (fun i j => if T.C i j=U.C i j then 0 else 1)
  rw [hA,hB,hC]
  omega
lemma responseDist_cycleXYZ (T U : DetTriangle) : responseDist (cycleXYZ T) (cycleXYZ U)=responseDist T U := by
  change responseDist (swapXY (swapYZ T)) (swapXY (swapYZ U))=_
  rw [responseDist_swapXY,responseDist_swapYZ]
lemma responseDist_cycleXZY (T U : DetTriangle) : responseDist (cycleXZY T) (cycleXZY U)=responseDist T U := by
  change responseDist (swapYZ (swapXY T)) (swapYZ (swapXY U))=_
  rw [responseDist_swapYZ,responseDist_swapXY]
lemma responseDist_applyPerm (T U : DetTriangle) (σ : Equiv.Perm (Fin 3)) :
    responseDist (applyPerm σ T) (applyPerm σ U)=responseDist T U := by
  unfold applyPerm
  split_ifs
  · rfl
  · exact responseDist_swapYZ T U
  · exact responseDist_swapXY T U
  · exact responseDist_cycleXYZ T U
  · exact responseDist_cycleXZY T U
  · exact responseDist_swapXZ T U
lemma responseDist_flipAll (T U : DetTriangle) : responseDist (flipAll T) (flipAll U)=responseDist T U := by
  simp only [responseDist_entries,flipAll,tableDist_flip]
lemma responseDist_symmetry (T U : DetTriangle) (g : Symmetry) :
    responseDist (g.apply T) (g.apply U)=responseDist T U := by
  unfold Symmetry.apply
  split_ifs <;> simp only [responseDist_flipAll,responseDist_applyPerm,responseDist_valueReindex]

lemma Symmetry.apply_injective (g : Symmetry) : Function.Injective g.apply := by
  intro T U h
  simpa only [g.apply_inv] using congrArg g.inv.apply h
lemma Symmetry.apply_inv_right (g : Symmetry) (T : DetTriangle) : g.apply (g.inv.apply T)=T := by
  apply g.inv.apply_injective
  rw [g.apply_inv]

end Paper15
