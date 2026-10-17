import Paper14.CoprimeErrorBounds
import Paper14.MoebiusTailBound
import Mathlib.Analysis.Asymptotics.Defs

open Filter Topology Finset Asymptotics
namespace Paper14
noncomputable section

lemma coprimePairCount_mobius_sum (n : ℕ) :
    (coprimePairCount n : ℝ) = ∑ d ∈ Finset.range (n+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)*
      (((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)*
      (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ) := by
  rw [coprimePairCount_eq_Ioc]
  apply coprime_rectangle_moebius
  · intro p hp
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hp).1
  · intro q hq
    exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hq).1
  · intro p hp
    exact (Finset.mem_Ioc.mp hp).2.trans (Nat.div_le_self n 3)

lemma sum_reciprocal_range (n : ℕ) :
    (∑ d ∈ Finset.range (n+1), (d : ℝ)⁻¹) = (harmonic n : ℝ) := by
  have hset : Finset.range (n+1) = insert 0 (Finset.Icc 1 n) := by
    ext d
    simp only [Finset.mem_range,Finset.mem_insert,Finset.mem_Icc]
    omega
  rw [hset,Finset.sum_insert (by simp)]
  simp only [Nat.cast_zero,inv_zero,zero_add,harmonic_eq_sum_Icc,Rat.cast_sum,Rat.cast_inv,Rat.cast_natCast]

lemma moebius_partial_error {n : ℕ} (hn : 0 < n) :
    |(∑ d ∈ Finset.range (n+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ)^2)-6/Real.pi^2| ≤ (n : ℝ)⁻¹ := by
  have hsum := hasSum_moebius_invSq.summable.sum_add_tsum_nat_add (n+1)
  rw [tsum_moebius_invSq] at hsum
  have heq : (∑ d ∈ Finset.range (n+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ)^2)-6/Real.pi^2 =
      -(∑' j : ℕ, ((ArithmeticFunction.moebius (j+(n+1)) : ℤ) : ℝ)/(((j+(n+1) : ℕ) : ℝ)^2)) := by linarith
  rw [heq,abs_neg,← Real.norm_eq_abs]
  exact moebius_invSq_norm_tail_le hn

lemma coprime_mobius_finite_error {n : ℕ} (hn : 0 < n) :
    |(coprimePairCount n : ℝ)-(n : ℝ)^2/12*
      (∑ d ∈ Finset.range (n+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ)^2)| ≤
      3*(n : ℝ)*(harmonic n : ℝ) := by
  have heq : (coprimePairCount n : ℝ)-(n : ℝ)^2/12*
      (∑ d ∈ Finset.range (n+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ)^2) =
      ∑ d ∈ Finset.range (n+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)*
        ((((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)*
         (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)-
         (n : ℝ)^2/(12*(d : ℝ)^2)) := by
    rw [coprimePairCount_mobius_sum,Finset.mul_sum,← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    ring
  rw [heq]
  calc
    _ ≤ ∑ d ∈ Finset.range (n+1), |((ArithmeticFunction.moebius d : ℤ) : ℝ)*
        ((((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)*
         (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)-
         (n : ℝ)^2/(12*(d : ℝ)^2))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.range (n+1), 3*(n : ℝ)/(d : ℝ) := by
      apply Finset.sum_le_sum
      intro d hd
      by_cases hd0 : d = 0
      · simp [hd0]
      · rw [abs_mul]
        have hm : |((ArithmeticFunction.moebius d : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        simpa only [one_mul] using mul_le_mul hm (appendix_product_error hn (Nat.pos_of_ne_zero hd0))
          (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.mul_sum,sum_reciprocal_range]

/-- Explicit error bound strengthening the normalized asymptotic to the
original Appendix A O(n log n) scale. -/
theorem coprimePairCount_error_bound {n : ℕ} (hn : 0 < n) :
    |(coprimePairCount n : ℝ)-(n : ℝ)^2/(2*Real.pi^2)| ≤ 4*(n : ℝ)*(1+Real.log n) := by
  let s : ℝ := ∑ d ∈ Finset.range (n+1), ((ArithmeticFunction.moebius d : ℤ) : ℝ)/(d : ℝ)^2
  have heq : (coprimePairCount n : ℝ)-(n : ℝ)^2/(2*Real.pi^2) =
      ((coprimePairCount n : ℝ)-(n : ℝ)^2/12*s)+(n : ℝ)^2/12*(s-6/Real.pi^2) := by ring
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  rw [heq]
  calc
    _ ≤ |(coprimePairCount n : ℝ)-(n : ℝ)^2/12*s|+|(n : ℝ)^2/12*(s-6/Real.pi^2)| := abs_add_le _ _
    _ ≤ 3*(n : ℝ)*(harmonic n : ℝ)+((n : ℝ)^2/12)*(n : ℝ)⁻¹ := by
      apply add_le_add (coprime_mobius_finite_error hn)
      rw [abs_mul,abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ)^2/12)]
      exact mul_le_mul_of_nonneg_left (moebius_partial_error hn) (by positivity)
    _ = 3*(n : ℝ)*(harmonic n : ℝ)+(n : ℝ)/12 := by field_simp
    _ ≤ 3*(n : ℝ)*(1+Real.log n)+(n : ℝ)/12 :=
      add_le_add_right (mul_le_mul_of_nonneg_left (harmonic_le_one_add_log n) (by positivity)) _
    _ ≤ _ := by nlinarith [mul_nonneg hn0.le hlog]

/-- The actual O(n log n) error term stated in original Appendix A (23). -/
theorem coprimePairCount_error_isBigO :
    (fun n : ℕ => (coprimePairCount n : ℝ)-(n : ℝ)^2/(2*Real.pi^2)) =O[atTop]
      (fun n : ℕ => (n : ℝ)*Real.log n) := by
  apply Asymptotics.isBigO_iff.mpr
  refine ⟨8,?_⟩
  have hlog : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ Real.log (n : ℝ) :=
    ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 1))
  filter_upwards [eventually_gt_atTop (0 : ℕ),hlog] with n hn hln
  rw [Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith : (0 : ℝ) ≤ Real.log n))]
  apply (coprimePairCount_error_bound hn).trans
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left hln hn0]

end
end Paper14
