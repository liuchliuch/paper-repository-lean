import Paper28.TreeSplitting
import Paper28.ShadowDifferential
import Paper28.JacobianContraction

/-! Native star base case of the tree Jacobian induction. Every leaf term
is zero on the sphere tangent plane and the center term is at most one. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open SimpleGraph
open scoped InnerProductSpace
attribute [local instance] Classical.propDecidable
variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq κ]

/-- The original full-dimensional Gram Jacobian of the explicit shadow
differential on a specified tangent plane. -/
def partitionJacobian (f : ι → κ) (u : EuclideanSpace ℝ ι)
    (S : Submodule ℝ (EuclideanSpace ℝ ι)) : ℝ :=
  frameJacobian (fun v : S => shadowDifferential f u v.val)

theorem partitionJacobian_nonneg (f : ι → κ) (u : EuclideanSpace ℝ ι)
    (S : Submodule ℝ (EuclideanSpace ℝ ι)) : 0 ≤ partitionJacobian f u S := Real.sqrt_nonneg _

theorem partitionJacobian_le_one (hFischer : FischerInput) (f : ι → κ)
    (u : EuclideanSpace ℝ ι) (S : Submodule ℝ (EuclideanSpace ℝ ι))
    (hn : 2 ≤ Module.finrank ℝ S) : partitionJacobian f u S ≤ 1 := by
  apply frameJacobian_contraction hFischer
  · intro v a
    simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  · intro v
    exact shadowDifferential_norm_le f u v.val
  · exact hn

theorem shadowDifferential_single_branch_zero [Subsingleton κ] (f : ι → κ)
    (u h : EuclideanSpace ℝ ι) (htan : ⟪u,h⟫_ℝ = 0) : shadowDifferential f u h = 0 := by
  ext b
  rw [shadowDifferential_apply]
  have hf : Finset.univ.filter (fun i => f i = b) = Finset.univ := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact iff_true_intro (Subsingleton.elim _ _)
  have hi : (∑ i, u i * h i) = 0 := by
    simpa [PiLp.inner_apply, RCLike.inner_apply, mul_comm] using htan
  rw [hf, hi, zero_div]
  rfl

theorem partitionJacobian_single_branch [Subsingleton κ] (f : ι → κ)
    (u : EuclideanSpace ℝ ι) (S : Submodule ℝ (EuclideanSpace ℝ ι))
    (hn : 0 < Module.finrank ℝ S) (htan : ∀ v : S, ⟪u,v.val⟫_ℝ = 0) :
    partitionJacobian f u S = 0 := by
  exact frameJacobian_of_zero (U := S) (V := EuclideanSpace ℝ κ)
    (fun v : S => shadowDifferential f u v.val)
    (fun v => shadowDifferential_single_branch_zero f u v.val (htan v)) hn

variable {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj]

def treeJacobian (hT : T.IsTree) (u : EuclideanSpace ℝ T.edgeSet)
    (S : Submodule ℝ (EuclideanSpace ℝ T.edgeSet)) (v : V) : ℝ :=
  partitionJacobian (treeBranch T hT v) u S

/-- The complete pointwise star case, with the original dimension threshold. -/
theorem treeJacobian_star (hFischer : FischerInput) (hT : T.IsTree) (c : V)
    (hc : StarCenter T c) (u : EuclideanSpace ℝ T.edgeSet)
    (S : Submodule ℝ (EuclideanSpace ℝ T.edgeSet)) (hn : 4 ≤ Module.finrank ℝ S)
    (htan : ∀ v : S, ⟪u,v.val⟫_ℝ = 0) : ∑ v, treeJacobian T hT u S v ≤ 1 := by
  have hleaf (v : V) (hv : v ≠ c) : treeJacobian T hT u S v = 0 := by
    letI : Subsingleton (T.neighborSet v) := hc.neighbors_subsingleton T v hv
    exact partitionJacobian_single_branch (treeBranch T hT v) u S (by omega) htan
  rw [Finset.sum_eq_single c]
  · exact partitionJacobian_le_one hFischer (treeBranch T hT c) u S (by omega)
  · intro v _ hv
    exact hleaf v hv
  · simp

end Paper28
