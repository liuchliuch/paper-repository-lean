import Paper37.EnvelopeBridge
import Paper37.RiskBounds
import Mathlib.NumberTheory.Harmonic.Bounds

/-! The exact all-zero output and its uniformly lower-order stationary KL
contribution, source Corollary D.4. -/
noncomputable section
namespace Paper37.ZeroHistory
open scoped BigOperators ENNReal
open Paper37.Renewal Paper37.Prediction Paper37.EnvelopeBridge Paper37.Boundary

lemma reciprocal_reflection (n : ℕ) :
    (∑ t ∈ Finset.Icc 1 n, (1 : ℚ) / ((n+1-t+1 : ℕ) : ℚ)) =
      ∑ j ∈ Finset.Icc 2 (n+1), (j:ℚ)⁻¹ := by
  apply Finset.sum_bij (fun t _ => n+2-t)
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    apply Finset.mem_Icc.mpr
    omega
  · intro t ht u hu heq
    have ht' := Finset.mem_Icc.mp ht
    have hu' := Finset.mem_Icc.mp hu
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨n+2-j, Finset.mem_Icc.mpr (by omega), by omega⟩
  · intro t ht
    have ht' := Finset.mem_Icc.mp ht
    have he : n+1-t+1 = n+2-t := by omega
    simp [he, one_div]

lemma harmonic_remove_first (n : ℕ) :
    harmonic (n+1) - 1 = ∑ j ∈ Finset.Icc 2 (n+1), (j:ℚ)⁻¹ := by
  rw [harmonic_eq_sum_Icc, ← Finset.Ico_add_one_right_eq_Icc,
    Finset.sum_eq_sum_Ico_succ_bot (by omega : 1 < n+1+1)]
  simp [Finset.Ico_add_one_right_eq_Icc]

/-- Exact formula D.5 for the actual suffix-averaged predictor D.1. -/
theorem predict_zeros (n : ℕ) :
    predict n (List.replicate n false) = (harmonic (n+1)-1)/n := by
  unfold predict
  congr 1
  calc
    (∑ t ∈ Finset.Icc 1 n,
        blockConditional (n+1) ((List.replicate n false).drop (n-t))) =
        ∑ t ∈ Finset.Icc 1 n, (1:ℚ) / ((n+1-t+1:ℕ):ℚ) := by
      apply Finset.sum_congr rfl
      intro t ht
      have ht' := Finset.mem_Icc.mp ht
      have hdrop : (List.replicate n false).drop (n-t) = List.replicate t false := by
        rw [List.drop_replicate]
        congr 1
        omega
      rw [hdrop, blockConditional_zeros (n+1) t (by omega)]
    _ = harmonic (n+1)-1 := (reciprocal_reflection n).trans (harmonic_remove_first n).symm

lemma predict_zeros_real_sum (n : ℕ) :
    (predict n (List.replicate n false) : ℝ) =
      (∑ j ∈ Finset.Icc 2 (n+1), 1/(j:ℝ))/(n:ℝ) := by
  rw [predict_zeros, harmonic_remove_first]
  push_cast
  simp only [one_div]

/-- Every suffix conditional on the all-zero history lies between these two
reciprocal endpoints, and so does their average. -/
theorem predict_zeros_bounds {n : ℕ} (hn : 1 ≤ n) :
    1/((n:ℝ)+1) ≤ (predict n (List.replicate n false) : ℝ) ∧
      (predict n (List.replicate n false) : ℝ) ≤ 1/2 := by
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [predict_zeros_real_sum]
  constructor
  · apply (le_div_iff₀ hnp).2
    calc
      1/((n:ℝ)+1)*(n:ℝ) = ∑ _j ∈ Finset.Icc 2 (n+1), 1/((n:ℝ)+1) := by
        simp
        ring
      _ ≤ ∑ j ∈ Finset.Icc 2 (n+1), 1/(j:ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        have hj' := Finset.mem_Icc.mp hj
        apply one_div_le_one_div_of_le
        · exact_mod_cast (show 0 < j by omega)
        · exact_mod_cast hj'.2
  · apply (div_le_iff₀ hnp).2
    calc
      (∑ j ∈ Finset.Icc 2 (n+1), 1/(j:ℝ)) ≤ ∑ _j ∈ Finset.Icc 2 (n+1), (1/2:ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        apply one_div_le_one_div_of_le (by norm_num)
        exact_mod_cast (Finset.mem_Icc.mp hj).1
      _ = 1/2*(n:ℝ) := by simp; ring

/-- The harmonic upper bound gives the logarithmic scale of the zero-history
prediction, with its exact finite-sample denominator. -/
theorem predict_zeros_le_log {n : ℕ} (hn : 1 ≤ n) :
    (predict n (List.replicate n false) : ℝ) ≤ Real.log ((n:ℝ)+1)/(n:ℝ) := by
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  rw [predict_zeros]
  push_cast
  apply (div_le_div_iff_of_pos_right hnp).2
  have hh := harmonic_le_one_add_log (n+1)
  push_cast at hh
  linarith

lemma neg_log_one_sub_le {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1/2) :
    -Real.log (1-q) ≤ 2*q := by
  have hp : 0 < 1-q := by linarith
  have hlo := Real.one_sub_inv_le_log_of_pos hp
  have hinv : 1/(1-q) ≤ 1+2*q := by
    apply (div_le_iff₀ hp).2
    have hprod := mul_nonneg hq0 (show 0 ≤ 1-2*q by linarith)
    nlinarith
  rw [← one_div] at hlo
  linarith

/-- The finite weighted KL estimate used for the actual zero-history event.
The joint event/renewal mass `w*p` is controlled by the stationary boundary. -/
lemma weighted_kl_le {n : ℕ} (hn : 1 ≤ n) {w p q : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hwp : w*p ≤ 1/((n:ℝ)+1))
    (hqlo : 1/((n:ℝ)+1) ≤ q) (hqhi : q ≤ 1/2)
    (hql : q ≤ Real.log ((n:ℝ)+1)/(n:ℝ)) :
    w * klReal p q ≤ 3 * Real.log ((n:ℝ)+1)/(n:ℝ) := by
  have hnp : (0:ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn1p : 0 < (n:ℝ)+1 := by positivity
  have hq0 : 0 < q := (one_div_pos.mpr hn1p).trans_le hqlo
  have hq1 : q < 1 := by linarith
  have hL : 0 ≤ Real.log ((n:ℝ)+1) := Real.log_nonneg (by have := Nat.cast_nonneg (α:=ℝ) n; linarith)
  have hlogq : -Real.log q ≤ Real.log ((n:ℝ)+1) := by
    rw [← Real.log_inv]
    apply Real.log_le_log (inv_pos.mpr hq0)
    rw [← one_div]
    apply (div_le_iff₀ hq0).2
    have := (div_le_iff₀ hn1p).mp hqlo
    nlinarith
  have hlog1q := neg_log_one_sub_le hq0.le hqhi
  have hwp0 : 0 ≤ w*p := mul_nonneg hw0 hp0
  have hwcomp0 : 0 ≤ w*(1-p) := mul_nonneg hw0 (by linarith)
  have hwcomp1 : w*(1-p) ≤ 1 := by nlinarith
  have hpart1 := mul_le_mul_of_nonneg_left hlogq hwp0
  have hpart2 := mul_le_mul_of_nonneg_left hlog1q hwcomp0
  have hpart2' := mul_le_mul_of_nonneg_right hwcomp1 (show 0 ≤ 2*q by positivity)
  have hent := mul_nonneg hw0 (Real.binEntropy_nonneg hp0 hp1)
  have hcross := klReal_eq_crossEntropy (p := p) hq0.ne' (ne_of_lt hq1)
  have hbound : w*klReal p q ≤ (w*p)*Real.log ((n:ℝ)+1) + 2*q := by
    rw [hcross]
    nlinarith
  have hpart3 := mul_le_mul_of_nonneg_right hwp hL
  have hden : 1/((n:ℝ)+1) ≤ 1/(n:ℝ) := one_div_le_one_div_of_le hnp (by linarith)
  have hpart4 := mul_le_mul_of_nonneg_right hden hL
  calc
    w*klReal p q ≤ w*p*Real.log ((n:ℝ)+1) + 2*q := hbound
    _ ≤ (1/((n:ℝ)+1))*Real.log ((n:ℝ)+1) + 2*q := add_le_add_right hpart3 _
    _ ≤ (1/(n:ℝ))*Real.log ((n:ℝ)+1) + 2*(Real.log ((n:ℝ)+1)/(n:ℝ)) :=
      add_le_add hpart4 (mul_le_mul_of_nonneg_left hql (by norm_num))
    _ = _ := by ring

lemma stationary_zero_joint_le (μ : Law) (n : ℕ) :
    blockMass μ (List.replicate n false) * conditional μ (List.replicate n false) ≤
      1/((n:ℝ)+1) := by
  by_cases hr : 0 < residual μ n
  · exact stationary_zero_weighted_parameter μ n hr
  · have he : residual μ n = 0 := le_antisymm (le_of_not_gt hr) (residual_nonneg μ n)
    simp [blockMass_zeros, he]
    positivity

/-- The source D.4 all-zero contribution is uniformly lower order. This is an
explicit finite-sample bound for every finite-mean stationary renewal law. -/
theorem zero_contribution_le (μ : Law) {n : ℕ} (hn : 1 ≤ n) :
    blockMass μ (List.replicate n false) *
      klReal (conditional μ (List.replicate n false))
        (predict n (List.replicate n false) : ℝ) ≤
      3 * Real.log ((n:ℝ)+1)/(n:ℝ) := by
  exact weighted_kl_le hn (blockMass_nonneg μ _) (blockMass_le_one μ _)
    (conditional_mem_unitInterval μ _).1 (conditional_mem_unitInterval μ _).2
    (stationary_zero_joint_le μ n) (predict_zeros_bounds hn).1
    (predict_zeros_bounds hn).2 (predict_zeros_le_log hn)

/-- The same uniform event bound for the extended-value binary KL used in the
paper's risk definition. The predictor is interior, including at small n. -/
theorem zero_contribution_kl_le (μ : Law) {n : ℕ} (hn : 1 ≤ n) :
    ENNReal.ofReal (blockMass μ (List.replicate n false)) *
      kl (conditional μ (List.replicate n false)) (predict n (List.replicate n false) : ℝ) ≤
      ENNReal.ofReal (3 * Real.log ((n:ℝ)+1)/(n:ℝ)) := by
  have hn1p : (0:ℝ) < (n:ℝ)+1 := by positivity
  have hq0 : 0 < (predict n (List.replicate n false) : ℝ) :=
    (one_div_pos.mpr hn1p).trans_le (predict_zeros_bounds hn).1
  have hq1 : (predict n (List.replicate n false) : ℝ) < 1 := by
    linarith [(predict_zeros_bounds hn).2]
  rw [kl, if_neg (by simp [hq0.ne', ne_of_lt hq1])]
  rw [← ENNReal.ofReal_mul (blockMass_nonneg μ _)]
  exact ENNReal.ofReal_le_ofReal (zero_contribution_le μ hn)

end Paper37.ZeroHistory
