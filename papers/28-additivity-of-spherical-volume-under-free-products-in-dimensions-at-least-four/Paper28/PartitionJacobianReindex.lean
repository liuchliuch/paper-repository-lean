import Paper28.TreeJacobianBase
import Paper28.ShadowReindex
import Paper28.JacobianIsometries

/-! Exact covariance of the genuine full-dimensional shadow Jacobian under
source and target coordinate isometries, including the actual image plane. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {ι ι' κ κ' : Type*} [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
  [DecidableEq κ] [DecidableEq κ']

theorem partitionJacobian_reindex (e : ι ≃ ι') (q : κ ≃ κ')
    (g : ι → κ) (f : ι' → κ') (hroute : ∀ i, q (g i) = f (e i))
    (u : EuclideanSpace ℝ ι) (S : Submodule ℝ (EuclideanSpace ℝ ι)) :
    partitionJacobian g u S =
      partitionJacobian f (reindexCoordinates e u)
        (S.map (reindexCoordinates e).toLinearEquiv.toLinearMap) := by
  let P := reindexCoordinates e
  let S' := S.map P.toLinearEquiv.toLinearMap
  let E : S ≃ₗᵢ[ℝ] S' := P.submoduleMap S
  let f' := fun v : S' => shadowDifferential f (P u) v.val
  have hf : PreservesFrameSums f' := by
    intro v a
    simp only [f', Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]
  change frameJacobian (fun v : S => shadowDifferential g u v.val) = frameJacobian f'
  calc
    _ = frameJacobian (fun v : S => f' (E v)) := by
      apply frameJacobian_congr_inner
      intro v w
      exact shadowDifferential_reindex_inner e q g f hroute u v.val w.val
    _ = _ := by
      conv_rhs => rw [frameJacobian_eq_gram_basis f' hf ((stdOrthonormalBasis ℝ S).map E)]
      rfl

end Paper28
