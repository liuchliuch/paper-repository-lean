import Paper29.SeedCompression

noncomputable section
open scoped BigOperators ENNReal
namespace Paper29.ProcessTools

/-- Finite distributional averaging against an extended upper bound, including
∞, without any exchange of an infinite supremum and an expectation. -/
theorem ofReal_weighted_average_le {I E : Type} [Fintype I] [Fintype E]
    (θ : I → ℝ) (hθ : ∀ i,0 ≤ θ i) (hsθ : ∑ i,θ i=1)
    (q : E → ℝ) (hq : ∀ e,0 ≤ q e) (cost : I → E → ℝ) (hc : ∀ i e,0 ≤ cost i e)
    (M : ℝ≥0∞) (hM : ∀ i,(∑ e,ENNReal.ofReal (q e)*ENNReal.ofReal (cost i e)) ≤ M) :
    ENNReal.ofReal (∑ i,θ i*(∑ e,q e*cost i e)) ≤ M := by
  have he (i : I) : ENNReal.ofReal (∑ e,q e*cost i e) =
      ∑ e,ENNReal.ofReal (q e)*ENNReal.ofReal (cost i e) := by
    rw [ENNReal.ofReal_sum_of_nonneg (fun e _ => mul_nonneg (hq e) (hc i e))]
    exact Finset.sum_congr rfl (fun e _ => ENNReal.ofReal_mul (hq e))
  rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => mul_nonneg (hθ i)
    (Finset.sum_nonneg (fun e _ => mul_nonneg (hq e) (hc i e))))]
  simp_rw [ENNReal.ofReal_mul (hθ _),he]
  calc
    _ ≤ ∑ i,ENNReal.ofReal (θ i)*M := Finset.sum_le_sum (fun i _ => mul_le_mul_left' (hM i) _)
    _ = (∑ i,ENNReal.ofReal (θ i))*M := (Finset.sum_mul _ _ _).symm
    _ = M := by rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ => hθ i),hsθ,ENNReal.ofReal_one,one_mul]

end Paper29.ProcessTools
namespace Paper29.Transcript

theorem queryCount_nonneg {E I R : Type} (policy : Policy E I R) (e : E) (b : I → R) (n : ℕ) :
    0 ≤ queryCount policy e b n := by
  apply Finset.sum_nonneg
  intro t _
  split_ifs <;> norm_num

end Paper29.Transcript
