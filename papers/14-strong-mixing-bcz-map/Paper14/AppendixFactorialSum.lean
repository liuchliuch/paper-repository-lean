import Paper14.AppendixCountBasic
import Paper14.BoundedProductLimits

open MeasureTheory Finset
namespace Paper14
noncomputable section

lemma bernoulli_sum_factorial {ι : Type*} [DecidableEq ι] (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i ∈ s,(a i)^2 = a i) :
    (∑ i ∈ s,a i)*((∑ i ∈ s,a i)-1) =
      ∑ i ∈ s,∑ j ∈ s,if i=j then 0 else a i*a j := by
  have hrow (i : ι) (hi : i ∈ s) :
      (∑ j ∈ s,if i=j then (0 : ℝ) else a i*a j) = a i*(∑ j ∈ s,a j)-(a i)^2 := by
    calc
      _ = ∑ j ∈ s,(a i*a j-(if i=j then (a i)^2 else 0)) := by
        apply Finset.sum_congr rfl
        intro j hj
        by_cases hij : i=j
        · subst j; simp [pow_two]
        · simp [hij]
      _ = _ := by rw [Finset.sum_sub_distrib,← Finset.mul_sum]; simp [hi]
  rw [Finset.sum_congr rfl hrow,Finset.sum_sub_distrib,← Finset.sum_mul,
    Finset.sum_congr rfl ha]
  ring

lemma nat_factorial_real_mono {k l : ℕ} (hkl : k ≤ l) :
    (k : ℝ)*((k : ℝ)-1) ≤ (l : ℝ)*((l : ℝ)-1) := by
  have hR : (k : ℝ) ≤ l := by exact_mod_cast hkl
  by_cases hk : k=0
  · subst k
    rcases Nat.eq_zero_or_pos l with hl | hl
    · simp [hl]
    · have hlR : (1 : ℝ) ≤ l := by exact_mod_cast hl
      have hh := mul_nonneg (Nat.cast_nonneg l : (0 : ℝ) ≤ l) (by linarith : (0 : ℝ) ≤ l-1)
      simpa using hh
  · have hkR : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
    have hh := mul_nonneg (sub_nonneg.mpr hR) (by linarith : (0 : ℝ) ≤ (l : ℝ)+k-1)
    nlinarith

lemma integrable_ZCount_factorial (n : ℕ) (α : ℝ) (μ : Measure (ℝ × ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun x => (ZCount n α x : ℝ)*((ZCount n α x : ℝ)-1)) μ := by
  let C : ℝ := (Finset.Icc (-(4*n : ℤ)) (4*n) ×ˢ Finset.Icc (1 : ℤ) (2*n)).card
  apply integrable_of_measurable_bound ((measurable_ZCount_real n α).mul ((measurable_ZCount_real n α).sub_const 1))
    (C*(C+1))
  intro x
  have hx : (0 : ℝ) ≤ ZCount n α x := Nat.cast_nonneg _
  have hC : (ZCount n α x : ℝ) ≤ C := by
    dsimp [C]
    exact_mod_cast ZCount_le_box_card n α x
  rw [norm_mul,Real.norm_of_nonneg hx,Real.norm_eq_abs]
  have habs : |(ZCount n α x : ℝ)-1| ≤ C+1 := by
    calc
      _ ≤ |(ZCount n α x : ℝ)|+|1| := abs_sub _ _
      _ ≤ C+1 := by rw [abs_of_nonneg hx,abs_one]; linarith
  exact mul_le_mul hC habs (abs_nonneg _) (hx.trans hC)

end
end Paper14
