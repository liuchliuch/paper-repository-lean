import Paper28.TreeJacobianStep
import Paper28.CutJacobian
import Paper28.CutVertices

/-! The paper-owned finite-tree n-Jacobian inequality on every compatible
coordinate stratum. The induction uses actual retained subtrees, native
strict cardinal decrease, actual cut maps, and the proved rank/chain rules. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
universe u

/-- Pointwise coordinate-stratum form of Lemma 2.3. The only external
parameter is the disclosed classical Fischer determinant inequality. -/
theorem treeJacobian_bound (hFischer : FischerInput) {V : Type u} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] (hT : T.IsTree) (z : EuclideanSpace ℝ T.edgeSet)
    (S : Submodule ℝ (EuclideanSpace ℝ T.edgeSet)) (hn : 4 ≤ Module.finrank ℝ S)
    (htan : ∀ h : S, ⟪z,h.val⟫_ℝ = 0)
    (hzero : ∀ i, z i = 0 → ∀ h : S, h.val i = 0) :
    ∑ x, treeJacobian T hT z S x ≤ 1 := by
  let P (m : ℕ) : Prop := ∀ (W : Type u) [Fintype W] [DecidableEq W] (U : SimpleGraph W) [DecidableRel U.Adj] (hU : U.IsTree),
    Nat.card W = m → ∀ (a : EuclideanSpace ℝ U.edgeSet)
      (E : Submodule ℝ (EuclideanSpace ℝ U.edgeSet)),
      4 ≤ Module.finrank ℝ E → (∀ h : E, ⟪a,h.val⟫_ℝ = 0) →
      (∀ i, a i = 0 → ∀ h : E, h.val i = 0) → ∑ x, treeJacobian U hU a E x ≤ 1
  have hP : ∀ m, P m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro W _ _ U _ hU hcard a E hdim ht hz
      rcases star_or_internal_edge U hU.isConnected with ⟨c,hc⟩ | ⟨v,w,hedge⟩
      · exact treeJacobian_star U hFischer hU c hc a E hdim ht
      · have hvw := hedge.1
        obtain ⟨hleft,hright⟩ := internal_edge_card_decreases U hU v w hedge
        have hL := ih (Nat.card (retainedSide U v w)) (by omega)
        have hR := ih (Nat.card (retainedSide U w v)) (by omega)
        have hsubL : ∀ (b : EuclideanSpace ℝ (retainedTree U v w).edgeSet)
            (F : Submodule ℝ (EuclideanSpace ℝ (retainedTree U v w).edgeSet)),
            4 ≤ Module.finrank ℝ F → (∀ h : F, ⟪b,h.val⟫_ℝ = 0) →
            (∀ i, b i = 0 → ∀ h : F, h.val i = 0) →
            ∑ x, treeJacobian (retainedTree U v w) (retainedTree_isTree U hU v w hvw) b F x ≤ 1 :=
          hL (retainedSide U v w) (retainedTree U v w) (retainedTree_isTree U hU v w hvw) rfl
        have hsubR : ∀ (b : EuclideanSpace ℝ (retainedTree U w v).edgeSet)
            (F : Submodule ℝ (EuclideanSpace ℝ (retainedTree U w v).edgeSet)),
            4 ≤ Module.finrank ℝ F → (∀ h : F, ⟪b,h.val⟫_ℝ = 0) →
            (∀ i, b i = 0 → ∀ h : F, h.val i = 0) →
            ∑ x, treeJacobian (retainedTree U w v) (retainedTree_isTree U hU w v hvw.symm) b F x ≤ 1 :=
          hR (retainedSide U w v) (retainedTree U w v) (retainedTree_isTree U hU w v hvw.symm) rfl
        rw [sum_cut_sides U hU v w hvw]
        exact (add_le_add
          (treeJacobian_side_of_smaller_tree U hU v w hvw a E hdim ht hsubL)
          (treeJacobian_side_of_smaller_tree U hU w v hvw.symm a E hdim ht hsubR)).trans
            (cut_partitions_nJacobian U hFischer hU v w hvw a E hdim ht hz)
  exact hP (Nat.card V) V T hT rfl z S hn htan hzero

end Paper28
