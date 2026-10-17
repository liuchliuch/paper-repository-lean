import Paper14.MoebiusSeries
import Paper14.SieveVariance
import Mathlib.Analysis.PSeries

open Filter Topology Finset
namespace Paper14
noncomputable section

lemma invSq_tail_le {n : ℕ} (hn : 0 < n) :
    (∑' j : ℕ, (((j+(n+1) : ℕ) : ℝ)^2)⁻¹) ≤ (n : ℝ)⁻¹ := by
  have hs : Summable (fun j : ℕ => (((j+(n+1) : ℕ) : ℝ)^2)⁻¹) :=
    summable_invSq.comp_injective (fun a b h => Nat.add_right_cancel h)
  apply hs.tsum_le_of_sum_range_le
  intro J
  have heq : (∑ j ∈ Finset.range J, (((j+(n+1) : ℕ) : ℝ)^2)⁻¹) =
      ∑ j ∈ Finset.Ioc n (n+J), ((j : ℝ)^2)⁻¹ := by
    have hset : Finset.Ioc n (n+J) = Finset.Ico (n+1) (n+1+J) := by
      ext j
      simp only [Finset.mem_Ico,Finset.mem_Ioc]
      omega
    rw [hset,Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel_left]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.add_comm j (n+1)]
  rw [heq]
  exact (sum_Ioc_inv_sq_le_sub hn.ne' (Nat.le_add_right n J)).trans
    (sub_le_self _ (inv_nonneg.mpr (Nat.cast_nonneg _)))

lemma moebius_invSq_norm_tail_le {n : ℕ} (hn : 0 < n) :
    ‖∑' j : ℕ, ((ArithmeticFunction.moebius (j+(n+1)) : ℤ) : ℝ)/(((j+(n+1) : ℕ) : ℝ)^2)‖ ≤ (n : ℝ)⁻¹ := by
  have hs : Summable (fun j : ℕ => ((ArithmeticFunction.moebius (j+(n+1)) : ℤ) : ℝ)/(((j+(n+1) : ℕ) : ℝ)^2)) :=
    hasSum_moebius_invSq.summable.comp_injective (fun a b h => Nat.add_right_cancel h)
  have hb (j : ℕ) : ‖((ArithmeticFunction.moebius (j+(n+1)) : ℤ) : ℝ)/(((j+(n+1) : ℕ) : ℝ)^2)‖ ≤
      (((j+(n+1) : ℕ) : ℝ)^2)⁻¹ := by
    rw [norm_div,Real.norm_of_nonneg (sq_nonneg _)]
    have hm : ‖((ArithmeticFunction.moebius (j+(n+1)) : ℤ) : ℝ)‖ ≤ 1 := by
      rw [Real.norm_eq_abs]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := j+(n+1))
    simpa only [one_div] using div_le_div_of_nonneg_right hm (sq_nonneg (((j+(n+1) : ℕ) : ℝ)))
  exact (norm_tsum_le_tsum_norm hs.norm).trans
    (((hs.norm.tsum_le_tsum hb (summable_invSq.comp_injective (fun a b h => Nat.add_right_cancel h)))).trans (invSq_tail_le hn))

end
end Paper14
