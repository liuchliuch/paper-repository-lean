import Paper28.JacobianChain

/-! Basis-free Gram invariance and changes of domain by actual linear
isometries. These connect coordinate decompositions to the n-plane estimate. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped InnerProductSpace
variable {E F G K : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]
  [NormedAddCommGroup K] [InnerProductSpace ℝ K]
  [FiniteDimensional ℝ E]

theorem frameJacobian_congr_inner (f : E → F) (g : E → G)
    (h : ∀ x y, ⟪f x, f y⟫_ℝ = ⟪g x, g y⟫_ℝ) : frameJacobian f = frameJacobian g := by
  unfold frameJacobian
  congr 2
  ext i j
  exact h _ _

theorem frameJacobian_precompose_isometry [FiniteDimensional ℝ F] [FiniteDimensional ℝ G]
    (e : E ≃ₗᵢ[ℝ] F) (D : F →ₗ[ℝ] G) :
    frameJacobian (fun x => D (e x)) = frameJacobian D := by
  change frameJacobian (D.comp e.toLinearEquiv.toLinearMap) = frameJacobian D
  rw [frameJacobian_eq_linearJacobian, frameJacobian_eq_linearJacobian,
    linearJacobian_comp_of_finrank_eq _ _ e.toLinearEquiv.finrank_eq,
    linearJacobian_of_isometry _ e.norm_map, mul_one]

/-- Basis invariance with any finite orthonormal index set. This functional
form avoids reducing concrete subtype and L2 product linear-map instances. -/
theorem frameJacobian_eq_gram_basis
    {ι : Type*} [Fintype ι] [DecidableEq ι] (f : E → F)
    (hf : PreservesFrameSums f) (c : OrthonormalBasis ι ℝ E) :
    frameJacobian f = Real.sqrt (Matrix.gram ℝ (fun i => f (c i))).det := by
  classical
  let b := stdOrthonormalBasis ℝ E
  let D : E →ₗ[ℝ] F := b.toBasis.constr ℝ (fun i => f (b i))
  have hD (x : E) : D x = f x := by
    change b.toBasis.constr ℝ (fun i => f (b i)) x = f x
    rw [Module.Basis.constr_apply_fintype, ← hf]
    exact congrArg f (b.toBasis.sum_repr x)
  have hfun : (fun x => D x) = f := funext hD
  calc
    _ = frameJacobian D := congrArg frameJacobian hfun.symm
    _ = nJacobian D := (nJacobian_eq_gram D b).symm
    _ = Real.sqrt (Matrix.gram ℝ (fun i => D (c i))).det := nJacobian_eq_gram D c
    _ = _ := by simp_rw [hD]

/-- Functional change of domain by an actual linear isometry equivalence. -/
theorem frameJacobian_precompose_isometry_function
    [FiniteDimensional ℝ F]
    (e : E ≃ₗᵢ[ℝ] F) (f : F → G) (hf : PreservesFrameSums f) :
    frameJacobian (fun x => f (e x)) = frameJacobian f := by
  let b := stdOrthonormalBasis ℝ E
  rw [frameJacobian_eq_gram_basis f hf (b.map e)]
  rfl

end Paper28
