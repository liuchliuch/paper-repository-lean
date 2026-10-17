import Paper20.YoungRaising

namespace Paper20.YoungShapes
open Matrix Finset
noncomputable section
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

lemma vacuum_norm_step (n : ℕ) :
    (∑ μ : Shape (n+1), vacuum (n+1) μ^2)=
      (n+1:ℤ)*(∑ μ : Shape n, vacuum n μ^2) := by
  have he := Matrix.dotProduct_mulVec (vacuum n) (up n).transpose (vacuum (n+1))
  rw [Matrix.vecMul_transpose] at he
  change dotProduct (vacuum n) ((down n).mulVec (vacuum (n+1)))=
    dotProduct (vacuum (n+1)) (vacuum (n+1)) at he
  calc
    _ = dotProduct (vacuum (n+1)) (vacuum (n+1)) := by simp only [dotProduct,pow_two]
    _ = dotProduct (vacuum n) ((down n).mulVec (vacuum (n+1))) := he.symm
    _ = _ := by
      rw [down_vacuum]
      simp only [dotProduct,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,pow_two]
      apply Finset.sum_congr rfl
      intro μ hμ
      ring

/-- The squared norm of the actual finite Young-lattice path vector is
n!, derived from genuine cover combinatorics and matrix adjunction. This
is independent of the hook quotient; their identification is separate. -/
theorem vacuum_norm (n : ℕ) : (∑ μ : Shape n, vacuum n μ^2)=(n.factorial:ℤ) := by
  induction n with
  | zero => simp [vacuum,shape_zero_card]
  | succ n ih =>
    rw [vacuum_norm_step,ih,Nat.factorial_succ]
    push_cast
    rfl

end
end Paper20.YoungShapes
