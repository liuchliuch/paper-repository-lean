import Paper14.AppendixTotalCount
import Paper14.AppendixCrossMoment
import Paper14.BoundedProductLimits

open MeasureTheory Set Finset
namespace Paper14
noncomputable section

lemma integrable_appendixQCount_product {r : ℝ} (hr : (1 : ℝ)/2 < r) (q q' : ℕ)
    (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun x => (appendixQCount r q x : ℝ)*(appendixQCount r q' x : ℝ)) μ := by
  apply integrable_of_measurable_bound
    ((measurable_appendixQCount_real r q).mul (measurable_appendixQCount_real r q')) 1
  intro x
  have hq : (appendixQCount r q x : ℝ) ≤ 1 := by exact_mod_cast appendixQCount_le_one hr q x
  have hq' : (appendixQCount r q' x : ℝ) ≤ 1 := by exact_mod_cast appendixQCount_le_one hr q' x
  rw [norm_mul,Real.norm_of_nonneg (Nat.cast_nonneg _),Real.norm_of_nonneg (Nat.cast_nonneg _)]
  simpa using mul_le_mul hq hq' (Nat.cast_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)

lemma integral_appendixQCount_product (r : ℝ) (q q' : ℕ) :
    (∫ x in appendixAr r,(appendixQCount r q x : ℝ)*(appendixQCount r q' x : ℝ) ∂m) =
      ∑ p ∈ Finset.range (2*q),∑ p' ∈ Finset.range (2*q'),
        (m (appendixStrip r p q ∩ appendixStrip r p' q')).toReal := by
  classical
  let f : ℕ → ℕ → ℝ × ℝ → ℝ := fun p p' =>
    (appendixStrip r p q ∩ appendixStrip r p' q').indicator (fun _ => 1)
  have heq (x : ℝ × ℝ) : (appendixQCount r q x : ℝ)*(appendixQCount r q' x : ℝ) =
      ∑ p ∈ Finset.range (2*q),∑ p' ∈ Finset.range (2*q'), f p p' x := by
    rw [appendixQCount_real_eq_sum,appendixQCount_real_eq_sum,Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro p' hp'
    by_cases hx : x ∈ appendixStrip r p q <;> by_cases hx' : x ∈ appendixStrip r p' q' <;>
      simp [f,hx,hx']
  have hf (p p' : ℕ) : Integrable (f p p') (m.restrict (appendixAr r)) :=
    (integrable_const (1 : ℝ)).indicator
      ((measurableSet_appendixStrip r p q).inter (measurableSet_appendixStrip r p' q'))
  simp_rw [heq]
  rw [integral_finset_sum _ (fun p _ => integrable_finset_sum _ (fun p' _ => hf p p'))]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_finset_sum _ (fun p' _ => hf p p')]
  apply Finset.sum_congr rfl
  intro p' hp'
  have hsub : appendixStrip r p q ∩ appendixStrip r p' q' ⊆ appendixAr r := fun x hx => hx.1.1
  rw [show f p p' = (appendixStrip r p q ∩ appendixStrip r p' q').indicator (fun _ => (1 : ℝ)) from rfl,
    setIntegral_indicator ((measurableSet_appendixStrip r p q).inter (measurableSet_appendixStrip r p' q')),
    inter_eq_right.mpr hsub,setIntegral_const]
  simp [Measure.real]

/-- Uniform integral bound for any two distinct q's in the actual Appendix window. -/
lemma appendixQCount_cross_integral_bound {n q q' : ℕ} (hn : 0 < n) {α : ℝ}
    (hα : 0 < α) (hαs : α < 1/32) (hq : q ∈ Finset.Icc 1 (4*n)) (hq' : q' ∈ Finset.Icc 1 (4*n))
    (hqq : q ≠ q') :
    (∫ x in appendixAr (1-α/(n : ℝ)),
      (appendixQCount (1-α/(n : ℝ)) q x : ℝ)*(appendixQCount (1-α/(n : ℝ)) q' x : ℝ) ∂m) ≤
        20*(α/(n : ℝ))^2 := by
  rw [integral_appendixQCount_product]
  rcases lt_or_gt_of_ne hqq with hlt | hgt
  · exact appendix_crossMoment hn hα hαs (by have := (Finset.mem_Icc.mp hq).1; omega) hlt (Finset.mem_Icc.mp hq').2
  · rw [Finset.sum_comm]
    have hh := appendix_crossMoment hn hα hαs (by have := (Finset.mem_Icc.mp hq').1; omega) hgt (Finset.mem_Icc.mp hq).2
    simpa only [Set.inter_comm] using hh

end
end Paper14
