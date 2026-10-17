import Paper14.RectangleCount
import Paper14.MeasureOmega
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set Finset
open scoped ENNReal
open Classical
namespace Paper14
noncomputable section

lemma measurableSet_inZRect (n : ℕ) (ε : ℝ) (p q : ℤ) :
    MeasurableSet {x : ℝ × ℝ | inZRect n ε x p q} := by
  have hconst (P : Prop) : MeasurableSet {x : ℝ × ℝ | P} := by
    by_cases h : P <;> simp [h]
  have hu : Measurable (fun x : ℝ × ℝ => (q : ℝ)*x.2-(p : ℝ)*x.1) := by fun_prop
  have hv : Measurable (fun x : ℝ × ℝ => (q : ℝ)/x.1) := by fun_prop
  change MeasurableSet ({x : ℝ × ℝ | 0 < q} ∩ ({x | (q : ℝ) ≤ 2*n} ∩
    ({x | 1-ε < (q : ℝ)*x.2-(p : ℝ)*x.1} ∩
    ({x | (q : ℝ)*x.2-(p : ℝ)*x.1 ≤ 1} ∩
    ({x | 0 < (q : ℝ)/x.1} ∩ ({x | (q : ℝ)/x.1 ≤ 2*n} ∩ {x | IsCoprime p q}))))))
  exact (hconst _).inter ((hconst _).inter
    ((measurableSet_lt measurable_const hu).inter ((measurableSet_le hu measurable_const).inter
      ((measurableSet_lt measurable_const hv).inter ((measurableSet_le hv measurable_const).inter
        (hconst _))))))

lemma ZCount_eq_sum (n : ℕ) (α : ℝ) (x : ℝ × ℝ) :
    (ZCount n α x : ℝ) =
      ∑ pq ∈ (Finset.Icc (-(4*n : ℤ)) (4*n) ×ˢ Finset.Icc (1 : ℤ) (2*n)),
        if inZRect n (α/(n : ℝ)) x pq.1 pq.2 then (1 : ℝ) else 0 := by
  classical
  simp only [ZCount,Finset.card_eq_sum_ones,Finset.sum_filter,Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]

lemma measurable_ZCount_real (n : ℕ) (α : ℝ) :
    Measurable (fun x : ℝ × ℝ => (ZCount n α x : ℝ)) := by
  classical
  simp_rw [ZCount_eq_sum]
  exact Finset.measurable_sum _ (fun pq _ => measurable_const.piecewise (measurableSet_inZRect n _ _ _) measurable_const)

lemma ZCount_le_box_card (n : ℕ) (α : ℝ) (x : ℝ × ℝ) :
    ZCount n α x ≤ (Finset.Icc (-(4*n : ℤ)) (4*n) ×ˢ Finset.Icc (1 : ℤ) (2*n)).card := by
  classical
  exact Finset.card_filter_le _ _

lemma integrable_ZCount (n : ℕ) (α : ℝ) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun x => (ZCount n α x : ℝ)) μ := by
  apply Integrable.of_bound (measurable_ZCount_real n α).aestronglyMeasurable
    ((Finset.Icc (-(4*n : ℤ)) (4*n) ×ˢ Finset.Icc (1 : ℤ) (2*n)).card : ℝ)
  filter_upwards [] with x
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast ZCount_le_box_card n α x

end
end Paper14
