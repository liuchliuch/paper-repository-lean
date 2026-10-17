import GeometricMedianCoresets.NormedMedian
import GeometricMedianCoresets.IndexedSample
import GeometricMedianCoresets.VarianceBinomial

/-! The concrete outlier example in Remark 2.5, including its exact sampling probability. -/
noncomputable section
attribute [local instance] Classical.propDecidable
open scoped BigOperators
namespace GeometricMedianCoresets.Remark25

def population {n : ℕ} (hn : 0 < n) (R : ℝ) : Dataset ℝ n :=
  fun i => if i = ⟨0, hn⟩ then R else 0

lemma cost_population {n : ℕ} (hn : 0 < n) (R z : ℝ) :
    (normDist ℝ).cost (population hn R) z =
      (((n:ℝ) - 1) * |z| + |z - R|) / n := by
  unfold Dist.cost normDist
  have hpoint : ∀ i : Fin n, ‖z - population hn R i‖ =
      |z| + if i = ⟨0, hn⟩ then |z - R| - |z| else 0 := by
    intro i
    by_cases hi : i = ⟨0, hn⟩ <;> simp [population, hi, Real.norm_eq_abs]
  rw [Finset.sum_congr rfl (fun i _ => hpoint i), Finset.sum_add_distrib,
    Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  congr 1
  ring

/-- The origin is an attained median of the actual indexed outlier population. -/
lemma median_zero {m : ℕ} (hm : 2 ≤ m) {R : ℝ} (hR : 0 < R) :
    (normDist ℝ).IsGeometricMedian (population (by omega : 0 < 2*m) R) 0 := by
  intro z
  rw [cost_population, cost_population]
  simp only [abs_zero, sub_zero, zero_sub, mul_zero, zero_add, abs_neg, abs_of_pos hR]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  have htri : R ≤ |z| + |z - R| := by
    have h := abs_add_le z (R - z)
    rw [show z + (R - z) = R by ring, abs_of_pos hR, abs_sub_comm R z] at h
    exact h
  have hmR : (2:ℝ) ≤ m := by exact_mod_cast hm
  push_cast
  have hmul := mul_nonneg (by linarith : 0 ≤ 2 * (m:ℝ) - 2) (abs_nonneg z)
  nlinarith only [htri, hmul]

/-- The exact probability of missing any fixed index under the uniform subset law. -/
lemma miss_probability {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (hmn : m ≤ n) (i : Fin n) :
    ((((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun I => i ∉ I)).card : ℝ) /
      (n.choose m : ℝ) = 1 - (m:ℝ) / n := by
  have hc := Finset.filter_card_add_filter_neg_card_eq_card
    (s := (Finset.univ : Finset (Fin n)).powersetCard m) (fun I => i ∈ I)
  rw [VarianceCount.card_filter_mem n m i hm hmn] at hc
  have hsum : ((n-1).choose (m-1) : ℝ) +
      ((((Finset.univ : Finset (Fin n)).powersetCard m).filter (fun I => i ∉ I)).card : ℝ) =
      (n.choose m : ℝ) := by
    have hcard : ((Finset.univ : Finset (Fin n)).powersetCard m).card = n.choose m := by simp
    rw [hcard] at hc
    exact_mod_cast hc
  have hb := VarianceBinomial.choose_mul_eq_choose_pred n m hm hmn
  have hbR : (n.choose m : ℝ) * m = ((n-1).choose (m-1) : ℝ) * n := by exact_mod_cast hb
  have hnR : (n:ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hC : (n.choose m : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hmn).ne'
  field_simp
  nlinarith [hsum, hbR]

/-- The outlier in a `2m`-point population is missed with probability exactly one half. -/
theorem miss_half {m : ℕ} (hm : 2 ≤ m) :
    ((((Finset.univ : Finset (Fin (2*m))).powersetCard m).filter
      (fun I => (⟨0, by omega⟩ : Fin (2*m)) ∉ I)).card : ℝ) / ((2*m).choose m : ℝ) = 1/2 := by
  rw [miss_probability (by omega) (by omega) (by omega)]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  push_cast
  field_simp
  norm_num

lemma sample_cost_of_miss {n : ℕ} (hn : 0 < n) (R : ℝ) (I : Finset (Fin n))
    (hI : 0 < I.card) (hmiss : (⟨0, hn⟩ : Fin n) ∉ I) (z : ℝ) :
    (normDist ℝ).cost (indexedSample (population hn R) I) z = |z| := by
  have hz : indexedSample (population hn R) I = fun _ => (0:ℝ) := by
    funext j
    have hne : ((I.equivFin.symm j).val : Fin n) ≠ ⟨0, hn⟩ := by
      intro h
      have hj := (I.equivFin.symm j).property
      rw [h] at hj
      exact hmiss hj
    simp [indexedSample, population, hne]
  rw [hz]
  unfold Dist.cost normDist
  simp only [sub_zero, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Real.norm_eq_abs]
  have hcard : (I.card:ℝ) ≠ 0 := by exact_mod_cast hI.ne'
  field_simp

/-- The location-dependent error is exactly twice OPT on the half-probability event. -/
theorem comparison_error {m : ℕ} (hm : 2 ≤ m) {R : ℝ} (hR : 0 < R)
    (I : Finset (Fin (2*m))) (hI : I.card = m)
    (hmiss : (⟨0, by omega⟩ : Fin (2*m)) ∉ I) {z : ℝ} (hz : R ≤ z) :
    |(normDist ℝ).delta (population (by omega : 0 < 2*m) R)
      (indexedSample (population (by omega : 0 < 2*m) R) I) z 0| = R / m := by
  unfold Dist.delta
  rw [cost_population, cost_population, sample_cost_of_miss _ R I (by omega) hmiss,
    sample_cost_of_miss _ R I (by omega) hmiss]
  rw [abs_of_nonneg (by linarith : 0 ≤ z), abs_of_nonneg (by linarith : 0 ≤ z - R)]
  simp only [abs_zero, zero_sub, zero_mul, zero_add, abs_neg, abs_of_pos hR]
  have hmR : (m:ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have heq : ((((2*m:ℕ):ℝ)-1) * z + (z-R)) / (2*m:ℕ) - R / (2*m:ℕ) - (z - 0) =
      -(R / m) := by push_cast; field_simp; ring
  simp only [mul_zero, zero_add]
  rw [heq, abs_neg, abs_of_pos (div_pos hR (by exact_mod_cast (show 0 < m by omega)))]

/-- The optimum in the example is `R/(2m)`, so the error is exactly `2 OPT`. -/
theorem optimum_value {m : ℕ} (hm : 2 ≤ m) {R : ℝ} (hR : 0 < R) :
    (normDist ℝ).optimum (population (by omega : 0 < 2*m) R) = R / (2*m:ℕ) := by
  rw [← cost_median_eq_optimum _ _ 0 (median_zero hm hR), cost_population]
  simp [abs_of_pos hR]

/-- For every fixed nonnegative constant, the example exceeds the proposed absolute scale
once `m > C²/4`, exactly as stated in Remark 2.5. -/
theorem error_gt_opt_scale {m : ℕ} (hm : 0 < m) {R C : ℝ} (hR : 0 < R) (hC : 0 ≤ C)
    (hsize : C ^ 2 / 4 < m) :
    C * (R / (2 * (m:ℝ))) / Real.sqrt m < R / m := by
  have hmR : (0:ℝ) < m := by exact_mod_cast hm
  have hs : 0 < Real.sqrt (m:ℝ) := Real.sqrt_pos.2 hmR
  have hsquare := Real.sq_sqrt hmR.le
  have hcomp : C < 2 * Real.sqrt (m:ℝ) := by nlinarith
  apply (div_lt_iff₀ hs).2
  have hmul := mul_lt_mul_of_pos_right hcomp (div_pos hR (mul_pos (by norm_num : (0:ℝ) < 2) hmR))
  convert hmul using 1 <;> ring

/-- No fixed `C OPT / sqrt(m)` absolute comparison bound can have success probability
strictly above `1/2` uniformly over the paper's populations. -/
theorem outlier_obstruction (C : ℝ) (hC : 0 ≤ C) :
    ∃ (m : ℕ) (hm : 2 ≤ m),
      ((((Finset.univ : Finset (Fin (2*m))).powersetCard m).filter
        (fun I => (⟨0, by omega⟩ : Fin (2*m)) ∉ I)).card : ℝ) / ((2*m).choose m : ℝ) = 1/2 ∧
      ∀ I : Finset (Fin (2*m)), I.card = m → (⟨0, by omega⟩ : Fin (2*m)) ∉ I →
        C * (normDist ℝ).optimum (population (by omega : 0 < 2*m) 1) / Real.sqrt m <
          |(normDist ℝ).delta (population (by omega : 0 < 2*m) 1)
            (indexedSample (population (by omega : 0 < 2*m) 1) I) 1 0| := by
  obtain ⟨m, hmR⟩ := exists_nat_gt (max (2:ℝ) (C ^ 2 / 4))
  have hm : 2 ≤ m := by
    have h : (2:ℝ) < m := (le_max_left _ _).trans_lt hmR
    exact_mod_cast h.le
  refine ⟨m, hm, miss_half hm, ?_⟩
  intro I hI hmiss
  rw [comparison_error hm (by norm_num : (0:ℝ) < 1) I hI hmiss le_rfl,
    optimum_value hm (by norm_num : (0:ℝ) < 1)]
  push_cast
  exact error_gt_opt_scale (by omega) (by norm_num) hC ((le_max_right _ _).trans_lt hmR)

end GeometricMedianCoresets.Remark25
