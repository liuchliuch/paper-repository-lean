import Paper20.YoungPathCells

namespace Paper20.YoungShapes
open Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- The concrete cell bearing a given zero-based label in an actual path. -/
def position {n : ℕ} {μ : Shape n} (t : Path n μ) (i : Fin n) : ℕ × ℕ :=
  (cellList t).get ⟨i.val,by rw [cellList_length]; exact i.isLt⟩

lemma position_mem {n : ℕ} {μ : Shape n} (t : Path n μ) (i : Fin n) : position t i ∈ μ.val :=
  (mem_cellList n μ t _).mp (List.get_mem _ _)

lemma position_injective {n : ℕ} {μ : Shape n} (t : Path n μ) : Function.Injective (position t) := by
  intro i j he
  have h := (List.nodup_iff_injective_get.mp (cellList_nodup n μ t)) he
  exact Fin.ext (congrArg (fun a : Fin (cellList t).length => a.val) h)

/-- Actual labels and actual cells are in bijection. -/
def positionEquiv {n : ℕ} {μ : Shape n} (t : Path n μ) :
    Fin n ≃ {c : ℕ × ℕ // c ∈ μ.val.cells} :=
  Equiv.ofBijective (fun i => ⟨position t i,position_mem t i⟩) ⟨by
    intro i j he
    exact position_injective t (congrArg Subtype.val he),by
    intro c
    obtain ⟨i,hi⟩ := List.mem_iff_get.mp ((mem_cellList n μ t c.val).mpr c.property)
    refine ⟨⟨i.val,by exact lt_of_lt_of_eq i.isLt (cellList_length n μ t)⟩,?_⟩
    exact Subtype.ext hi⟩

@[simp] lemma position_filling {n : ℕ} {μ : Shape n} (t : Path n μ)
    (c : {c : ℕ × ℕ // c ∈ μ.val.cells}) :
    position t ((positionEquiv t).symm c)=c.val :=
  congrArg Subtype.val ((positionEquiv t).apply_symm_apply c)

lemma position_not_reverse {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (hij : i < j) : ¬position t j≤position t i := by
  exact (List.pairwise_iff_get.mp (cellList_order n μ t))
    ⟨i.val,by rw [cellList_length]; exact i.isLt⟩
    ⟨j.val,by rw [cellList_length]; exact j.isLt⟩ hij

/-- Comparable distinct cells occur in strictly increasing label order. -/
theorem index_lt_of_position_le {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (hij : position t i≤position t j) (hne : i≠j) : i < j := by
  by_contra hn
  have hji : j < i := lt_of_le_of_ne (le_of_not_gt hn) (Ne.symm hne)
  exact position_not_reverse t j i hji hij

/-- The actual filling defined by a path is strictly increasing in the
Young-diagram cell partial order, hence is a genuine standard filling. -/
theorem filling_strictMono {n : ℕ} {μ : Shape n} (t : Path n μ) :
    StrictMono (positionEquiv t).symm := by
  intro a b hab
  apply index_lt_of_position_le t _ _
  · simpa only [position_filling] using hab.le
  · intro he
    have hc := congrArg (positionEquiv t) he
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply] at hc
    exact hab.ne hc

/-- Actual zero-based content of a concrete Young-diagram cell. -/
def cellContent (c : ℕ × ℕ) : ℤ := (c.2:ℤ)-(c.1:ℤ)

def pathContent {n : ℕ} {μ : Shape n} (t : Path n μ) (i : Fin n) : ℤ :=
  cellContent (position t i)

end
end Paper20.YoungShapes
