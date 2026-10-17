import Paper20.YoungAdjacentContents

namespace Paper20.YoungShapes
open Finset Paper20.YoungCorners
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-- There is no actual cell strictly between two consecutively labelled
cells in the cell partial order. -/
theorem no_intermediate_cell {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (hij : j.val=i.val+1)
    (c : {c : ℕ × ℕ // c ∈ μ.val.cells})
    (hac : position t i<c.val) (hcb : c.val<position t j) : False := by
  let k := (positionEquiv t).symm c
  have hk := position_filling t c
  have hik : i < k := by
    apply index_lt_of_position_le t i k
    · rw [hk]; exact hac.le
    · intro he
      have hp := congrArg (position t) he
      rw [hk] at hp
      exact hac.ne hp
  have hkj : k < j := by
    apply index_lt_of_position_le t k j
    · rw [hk]; exact hcb.le
    · intro he
      have hp := congrArg (position t) he
      rw [hk] at hp
      exact hcb.ne hp
  have hi' : i.val < k.val := hik
  have hj' : k.val < j.val := hkj
  omega

/-- Comparable consecutively labelled cells share an edge, rather than
merely lying somewhere in the same row, column, or southeast direction. -/
theorem adjacent_comparable_edge {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (hij : j.val=i.val+1) (hle : position t i≤position t j) :
    ((position t j).1=(position t i).1 ∧ (position t j).2=(position t i).2+1) ∨
      ((position t j).1=(position t i).1+1 ∧ (position t j).2=(position t i).2) := by
  let a := position t i
  let b := position t j
  have hrow : a.1≤b.1 := hle.1
  have hcol : a.2≤b.2 := hle.2
  have hab : a≠b := by
    intro he
    have hi := position_injective t he
    have hv := congrArg Fin.val hi
    omega
  have hrpos : a.1 < b.1 ∨ a.2 < b.2 := by
    by_contra hn
    push_neg at hn
    exact hab (Prod.ext (by omega) (by omega))
  by_cases hc : a.2 < b.2
  · have hm : (a.1,a.2+1) ∈ μ.val :=
      μ.val.isLowerSet (show (a.1,a.2+1)≤b from ⟨hrow,by omega⟩) (position_mem t j)
    have he : b=(a.1,a.2+1) := by
      by_contra hn
      apply no_intermediate_cell t i j hij ⟨(a.1,a.2+1),hm⟩
      · change a < (a.1,a.2+1)
        apply lt_iff_le_not_ge.mpr
        refine ⟨⟨le_rfl,by omega⟩,?_⟩
        intro h
        have := h.2
        omega
      · change (a.1,a.2+1) < b
        exact lt_of_le_of_ne ⟨hrow,by omega⟩ (Ne.symm hn)
    change (b.1=a.1 ∧ b.2=a.2+1) ∨ (b.1=a.1+1 ∧ b.2=a.2)
    have hfst := congrArg (fun c : ℕ × ℕ => c.1) he
    have hsnd := congrArg (fun c : ℕ × ℕ => c.2) he
    exact Or.inl ⟨hfst,hsnd⟩
  · have hce : a.2=b.2 := by omega
    have hr : a.1 < b.1 := hrpos.resolve_right hc
    have hm : (a.1+1,a.2) ∈ μ.val :=
      μ.val.isLowerSet (show (a.1+1,a.2)≤b from ⟨by omega,hcol⟩) (position_mem t j)
    have he : b=(a.1+1,a.2) := by
      by_contra hn
      apply no_intermediate_cell t i j hij ⟨(a.1+1,a.2),hm⟩
      · change a < (a.1+1,a.2)
        apply lt_iff_le_not_ge.mpr
        refine ⟨⟨by omega,le_rfl⟩,?_⟩
        intro h
        have := h.1
        omega
      · change (a.1+1,a.2) < b
        exact lt_of_le_of_ne ⟨by omega,hcol⟩ (Ne.symm hn)
    change (b.1=a.1 ∧ b.2=a.2+1) ∨ (b.1=a.1+1 ∧ b.2=a.2)
    have hfst := congrArg (fun c : ℕ × ℕ => c.1) he
    have hsnd := congrArg (fun c : ℕ × ℕ => c.2) he
    exact Or.inr ⟨hfst,hsnd⟩

/-- A forbidden adjacent standard-tableau exchange has precisely content
difference 1 or -1, the two scalar boundary cases of the Hecke action. -/
theorem adjacent_comparable_content {n : ℕ} {μ : Shape n} (t : Path n μ)
    (i j : Fin n) (hij : j.val=i.val+1) (hle : position t i≤position t j) :
    pathContent t j-pathContent t i=1 ∨ pathContent t j-pathContent t i= -1 := by
  have he := adjacent_comparable_edge t i j hij hle
  dsimp only [pathContent,cellContent]
  rcases he with ⟨hr,hc⟩ | ⟨hr,hc⟩
  · left; rw [hr,hc]; push_cast; ring
  · right; rw [hr,hc]; push_cast; ring

end
end Paper20.YoungShapes
