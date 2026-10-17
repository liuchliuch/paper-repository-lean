import Paper28.TreeCuts

/-! The actual original vertices are the disjoint union of the two cut
components. This supplies the exact finite-sum split in the tree induction. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
attribute [local instance] Classical.propDecidable
variable {V : Type*} (T : SimpleGraph V)

def cutVertexEquiv (hT : T.IsTree) (v w : V) (hvw : T.Adj v w) :
    cutSide T v w ⊕ cutSide T w v ≃ V where
  toFun := Sum.elim Subtype.val Subtype.val
  invFun x := if h : x ∈ cutSide T v w then .inl ⟨x,h⟩
    else .inr ⟨x, (cut_sides_cover T hT.isConnected v w x).resolve_left h⟩
  left_inv i := by
    rcases i with a | b
    · simp only [Sum.elim_inl, dif_pos a.property]
    · have hb : b.val ∉ cutSide T v w := fun h =>
        Set.disjoint_left.mp (cut_sides_disjoint T hT v w hvw) h b.property
      simp only [Sum.elim_inr, dif_neg hb]
  right_inv x := by
    by_cases hx : x ∈ cutSide T v w <;> simp [hx]

theorem sum_cut_sides [Fintype V] (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (f : V → ℝ) :
    (∑ x : V, f x) = (∑ x : cutSide T v w, f x.val) +
      (∑ x : cutSide T w v, f x.val) := by
  have h := Fintype.sum_equiv (cutVertexEquiv T hT v w hvw)
    (fun x => f (cutVertexEquiv T hT v w hvw x)) f (fun _ => rfl)
  rw [Fintype.sum_sum_type] at h
  exact h.symm

end Paper28
