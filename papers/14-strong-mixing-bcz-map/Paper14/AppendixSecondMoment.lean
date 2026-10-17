import Paper14.AppendixQCountIntegral
import Paper14.AppendixFactorialSum

open MeasureTheory Set Finset
open scoped ENNReal
namespace Paper14
noncomputable section

lemma appendixTotalCount_factorial_eq {r : ℝ} (hr : (1 : ℝ)/2 < r) (n : ℕ) (x : ℝ × ℝ) :
    (appendixTotalCount n r x : ℝ)*((appendixTotalCount n r x : ℝ)-1) =
      ∑ q ∈ Finset.Icc 1 (4*n),∑ q' ∈ Finset.Icc 1 (4*n),
        if q=q' then 0 else (appendixQCount r q x : ℝ)*(appendixQCount r q' x : ℝ) := by
  classical
  simp only [appendixTotalCount,Nat.cast_sum]
  apply bernoulli_sum_factorial (Finset.Icc 1 (4*n)) (fun q => (appendixQCount r q x : ℝ))
  intro q hq
  have hh := appendixQCount_le_one hr q x
  have hcases : appendixQCount r q x = 0 ∨ appendixQCount r q x = 1 := by omega
  rcases hcases with h | h <;> simp [h]

/-- The genuine factorial second moment (26), for F_2=Z_{2n,2α}. -/
theorem appendix_secondMoment {n : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hαs : α < 1/32) :
    (∫ x in appendixAr (1-α/(n : ℝ)),
      (ZCount (2*n) (2*α) x : ℝ)*((ZCount (2*n) (2*α) x : ℝ)-1) ∂m) ≤ 320*α^2 := by
  classical
  let r := 1-α/(n : ℝ)
  let Q := Finset.Icc 1 (4*n)
  let F : ℕ → ℕ → ℝ × ℝ → ℝ := fun q q' x =>
    if q=q' then 0 else (appendixQCount r q x : ℝ)*(appendixQCount r q' x : ℝ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hε : α/(n : ℝ) < 1/32 := by
    apply (div_lt_iff₀ hnR).mpr
    nlinarith
  have hr : (1 : ℝ)/2 < r := by dsimp [r]; linarith
  have hF (q q' : ℕ) : Integrable (F q q') (m.restrict (appendixAr r)) := by
    by_cases hqq : q=q'
    · simp [F,hqq]
    · simpa only [F,if_neg hqq] using integrable_appendixQCount_product hr q q' (m.restrict (appendixAr r))
  have hS : Integrable (fun x => (appendixTotalCount n r x : ℝ)*((appendixTotalCount n r x : ℝ)-1))
      (m.restrict (appendixAr r)) := by
    have heq : (fun x => (appendixTotalCount n r x : ℝ)*((appendixTotalCount n r x : ℝ)-1)) =
        (fun x => ∑ q ∈ Q,∑ q' ∈ Q,F q q' x) := by
      funext x
      exact appendixTotalCount_factorial_eq hr n x
    rw [heq]
    exact integrable_finset_sum _ (fun q _ => integrable_finset_sum _ (fun q' _ => hF q q'))
  have hmono := integral_mono_ae (integrable_ZCount_factorial (2*n) (2*α) (m.restrict (appendixAr r))) hS (by
    filter_upwards [ae_restrict_mem (measurableSet_appendixAr r)] with x hx
    exact nat_factorial_real_mono (appendix_F2_le_totalCount hn hα (by linarith) hx))
  have hupper : (∫ x in appendixAr r,
      (appendixTotalCount n r x : ℝ)*((appendixTotalCount n r x : ℝ)-1) ∂m) ≤ 320*α^2 := by
    simp_rw [appendixTotalCount_factorial_eq hr n]
    change (∫ x in appendixAr r,∑ q ∈ Q,∑ q' ∈ Q,F q q' x ∂m) ≤ _
    rw [integral_finset_sum _ (fun q _ => integrable_finset_sum _ (fun q' _ => hF q q'))]
    simp_rw [integral_finset_sum _ (fun q' _ => hF _ q')]
    calc
      _ ≤ ∑ q ∈ Q,∑ q' ∈ Q,20*(α/(n : ℝ))^2 := by
        apply Finset.sum_le_sum
        intro q hq
        apply Finset.sum_le_sum
        intro q' hq'
        by_cases hqq : q=q'
        · simp only [F,if_pos hqq,integral_zero]
          positivity
        · simpa only [F,if_neg hqq] using appendixQCount_cross_integral_bound hn hα hαs hq hq' hqq
      _ = 320*α^2 := by
        simp only [Finset.sum_const,nsmul_eq_mul]
        have hQ : (Q.card : ℝ) = 4*(n : ℝ) := by simp [Q]
        rw [hQ]
        field_simp [hnR.ne']
        ring
  exact hmono.trans hupper

end
end Paper14
