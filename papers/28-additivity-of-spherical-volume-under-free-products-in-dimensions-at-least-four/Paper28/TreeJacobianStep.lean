import Paper28.TreeDifferentialFactor
import Paper28.TreeJacobianBase
import Paper28.FrameJacobianChain
import Paper28.JacobianIsometries

/-! One side of the native tree induction. The smaller-tree hypothesis is
an induction hypothesis on that actual retained tree, never an external input.
Rank loss gives zero term by term; full rank uses the actual differential image. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
namespace Paper28
attribute [local irreducible] frameJacobian
open SimpleGraph
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

theorem treeJacobian_side_of_smaller_tree (hT : T.IsTree) (v w : V) (hvw : T.Adj v w)
    (u : EuclideanSpace ℝ T.edgeSet) (S : Submodule ℝ (EuclideanSpace ℝ T.edgeSet))
    (hn : 4 ≤ Module.finrank ℝ S) (htan : ∀ h : S, ⟪u,h.val⟫_ℝ = 0)
    (hSub : ∀ (z : EuclideanSpace ℝ (retainedTree T v w).edgeSet)
      (P : Submodule ℝ (EuclideanSpace ℝ (retainedTree T v w).edgeSet)),
      4 ≤ Module.finrank ℝ P → (∀ h : P, ⟪z,h.val⟫_ℝ = 0) →
      (∀ i, z i = 0 → ∀ h : P, h.val i = 0) →
      ∑ x, treeJacobian (retainedTree T v w) (retainedTree_isTree T hT v w hvw) z P x ≤ 1) :
    (∑ x : cutSide T v w, treeJacobian T hT u S x.val) ≤
      partitionJacobian (collapseEdge T v w hvw) u S := by
  let g := collapseEdge T v w hvw
  let D : S →ₗ[ℝ] EuclideanSpace ℝ (retainedTree T v w).edgeSet :=
    (shadowDifferential g u).comp S.subtype
  let z := finiteShadow g u
  let hR := retainedTree_isTree T hT v w hvw
  let j : cutSide T v w → retainedSide T v w := fun x => ⟨x.val, Or.inl x.property⟩
  let A (x : cutSide T v w) := shadowDifferential (treeBranch (retainedTree T v w) hR (j x)) z
  have hJac (x : cutSide T v w) : treeJacobian T hT u S x.val =
      frameJacobian (fun h : S => A x (D h)) := by
    apply frameJacobian_congr_inner
    intro h k
    exact treeDifferential_cut_inner T hT v w hvw x.val x.property u h.val k.val
  by_cases hD : Function.Injective D
  · let P := LinearMap.range D
    have hdim : 4 ≤ Module.finrank ℝ P := by rw [LinearMap.finrank_range_of_inj hD]; exact hn
    have ht : ∀ h : P, ⟪z,h.val⟫_ℝ = 0 := by
      rintro ⟨a, b, rfl⟩
      exact (shadowDifferential_tangent g u b.val).trans (htan b)
    have hz : ∀ i, z i = 0 → ∀ h : P, h.val i = 0 := by
      intro i hi h
      obtain ⟨b, hb⟩ := h.property
      rw [← hb]
      exact shadowDifferential_zero_coordinate g u b.val i hi
    have hbound := hSub z P hdim ht hz
    have hterm (x : cutSide T v w) : treeJacobian T hT u S x.val =
        treeJacobian (retainedTree T v w) hR z P (j x) * partitionJacobian g u S := by
      rw [hJac]
      have hchain := frameJacobian_comp_range D (A x) hD
      change frameJacobian (fun h : S => A x (D h)) =
        treeJacobian (retainedTree T v w) hR z P (j x) * partitionJacobian g u S at hchain
      exact hchain
    simp_rw [hterm]
    rw [← Finset.sum_mul]
    have hinj : Function.Injective j := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun q : retainedSide T v w => q.val) h
    have hsum : (∑ x : cutSide T v w, treeJacobian (retainedTree T v w) hR z P (j x)) ≤
        ∑ y, treeJacobian (retainedTree T v w) hR z P y := by
      rw [← Finset.sum_image hinj.injOn]
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      intro y _ _
      exact partitionJacobian_nonneg _ _ _
    have hj : 0 ≤ partitionJacobian g u S := partitionJacobian_nonneg g u S
    calc
      _ ≤ (∑ y, treeJacobian (retainedTree T v w) hR z P y) * partitionJacobian g u S :=
        mul_le_mul_of_nonneg_right hsum hj
      _ ≤ 1 * partitionJacobian g u S := mul_le_mul_of_nonneg_right hbound hj
      _ = _ := one_mul _
  · have hterm (x : cutSide T v w) : treeJacobian T hT u S x.val = 0 := by
      rw [hJac]
      have hchain := frameJacobian_comp_of_not_injective D (A x) hD
      exact hchain
    simp_rw [hterm]
    simp only [Finset.sum_const_zero]
    exact partitionJacobian_nonneg g u S

end Paper28
