import Paper28.CutPartitions
import Paper28.PartitionJacobianReindex
import Paper28.SplitJacobian

/-! The sharp full-dimensional estimate for the actual two edge-cut maps
of the original tree, rather than an abstract or supplied cut estimate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

theorem cut_partitions_nJacobian (hFischer : FischerInput) (hT : T.IsTree)
    (v w : V) (hvw : T.Adj v w) (u : EuclideanSpace ℝ T.edgeSet)
    (S : Submodule ℝ (EuclideanSpace ℝ T.edgeSet))
    (hn : 4 ≤ Module.finrank ℝ S) (htan : ∀ h : S, ⟪u,h.val⟫_ℝ = 0)
    (hzero : ∀ i, u i = 0 → ∀ h : S, h.val i = 0) :
    partitionJacobian (collapseEdge T v w hvw) u S +
      partitionJacobian (collapseEdge T w v hvw.symm) u S ≤ 1 := by
  let c := cutCoordinateEquiv T v w hvw
  let l := retainedCoordinateEquiv T hT v w hvw
  let r := rightRetainedCoordinateEquiv T hT v w hvw
  have hrL : ∀ i, l.symm (collapseEdge T v w hvw i) = splitLeft (c.symm i) := by
    intro i
    apply l.injective
    simp only [Equiv.apply_symm_apply]
    have h := cutPartition_left_route T hT v w hvw (c.symm i)
    change collapseEdge T v w hvw (c (c.symm i)) = l (splitLeft (c.symm i)) at h
    simpa only [Equiv.apply_symm_apply] using h
  have hrR : ∀ i, r.symm (collapseEdge T w v hvw.symm i) = splitRight (c.symm i) := by
    intro i
    apply r.injective
    simp only [Equiv.apply_symm_apply]
    have h := cutPartition_right_route T hT v w hvw (c.symm i)
    change collapseEdge T w v hvw.symm (c (c.symm i)) = r (splitRight (c.symm i)) at h
    simpa only [Equiv.apply_symm_apply] using h
  rw [partitionJacobian_reindex c.symm l.symm _ splitLeft hrL u S,
    partitionJacobian_reindex c.symm r.symm _ splitRight hrR u S]
  let P := reindexCoordinates c.symm
  let S' := S.map P.toLinearEquiv.toLinearMap
  let E : S ≃ₗᵢ[ℝ] S' := P.submoduleMap S
  have hdim : 4 ≤ Module.finrank ℝ S' := by rw [← E.toLinearEquiv.finrank_eq]; exact hn
  have ht : ∀ h : S', ⟪P u,h.val⟫_ℝ = 0 := by
    intro h
    obtain ⟨k, rfl⟩ := E.surjective h
    change ⟪P u,P k.val⟫_ℝ = 0
    rw [P.inner_map_map]
    exact htan k
  have hz : ∀ i, (P u) i = 0 → ∀ h : S', h.val i = 0 := by
    intro i hi h
    obtain ⟨k, rfl⟩ := E.surjective h
    change k.val (c i) = 0
    exact hzero (c i) hi k
  exact split_partitions_nJacobian hFischer (P u) S' hdim ht hz

end Paper28
