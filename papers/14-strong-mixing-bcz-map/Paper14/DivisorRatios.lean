import Paper14.PeriodicSums
import Paper14.DivisorWindows
import Mathlib.Algebra.Order.Floor.Semifield

open Filter Topology
namespace Paper14
noncomputable section

lemma nat_div_ratio (d : ℕ) :
    Tendsto (fun n : ℕ => ((n/d : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 ((d : ℝ)⁻¹)) := by
  by_cases hd : d = 0
  · simp [hd]
  have hdr : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_ne_zero hd
  have h := sieve_Q_ratio (K := 2*(d : ℝ)) (by positivity)
  have heq (n : ℕ) : 2*(n : ℝ)/(2*(d : ℝ)) = (n : ℝ)/(d : ℝ) := by ring
  simp only [heq,Nat.floor_div_eq_div] at h
  have hvalue : (2 : ℝ)/(2*(d : ℝ)) = (d : ℝ)⁻¹ := by field_simp
  simpa only [hvalue] using h

lemma nat_pred_ratio : Tendsto (fun n : ℕ => ((n-1 : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 1) := by
  have heq : (fun n : ℕ => ((n-1 : ℕ) : ℝ)/(n : ℝ)) =ᶠ[atTop]
      (fun n => 1-1/(n : ℝ)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    rw [Nat.cast_sub (by omega),Nat.cast_one]
    field_simp
  apply (tendsto_congr' heq).mpr
  simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub tendsto_one_div_atTop_nhds_zero_nat

lemma nat_pred_div_ratio (d : ℕ) :
    Tendsto (fun n : ℕ => (((n-1)/d : ℕ) : ℝ)/(n : ℝ)) atTop (𝓝 ((d : ℝ)⁻¹)) := by
  have hp : Tendsto (fun n : ℕ => n-1) atTop atTop := tendsto_sub_atTop_nat 1
  have h := ((nat_div_ratio d).comp hp).mul nat_pred_ratio
  apply (tendsto_congr' ?_).mpr (by simpa using h)
  filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
  have hpred : ((n-1 : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (show n-1 ≠ 0 by omega)
  field_simp [hpred]

/-- Exact normalized first-window multiple count asymptotic. -/
lemma appendix_p_multiples_ratio (d : ℕ) :
    Tendsto (fun n : ℕ => (((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)/(n : ℝ))
      atTop (𝓝 ((6*(d : ℝ))⁻¹)) := by
  have h := (nat_div_ratio (3*d)).sub (nat_div_ratio (6*d))
  have heq (n : ℕ) :
      (((Finset.Ioc (n/6) (n/3)).filter (fun p => d ∣ p)).card : ℝ)/(n : ℝ) =
        ((n/(3*d) : ℕ) : ℝ)/(n : ℝ)-((n/(6*d) : ℕ) : ℝ)/(n : ℝ) := by
    rw [Ioc_filter_dvd_card,Nat.cast_sub (Nat.div_le_div_right (show n/6 ≤ n/3 by omega)),sub_div]
    simp only [Nat.div_div_eq_div_mul]
  simp_rw [heq]
  convert h using 1
  by_cases hd : d = 0
  · simp [hd]
  · have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp
    ring

/-- Exact normalized second-window multiple count asymptotic. -/
lemma appendix_q_multiples_ratio (d : ℕ) :
    Tendsto (fun n : ℕ => (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)/(n : ℝ))
      atTop (𝓝 ((2*(d : ℝ))⁻¹)) := by
  have h := (nat_div_ratio d).sub (nat_pred_div_ratio (2*d))
  have heq (n : ℕ) :
      (((Finset.Ioc ((n-1)/2) n).filter (fun q => d ∣ q)).card : ℝ)/(n : ℝ) =
        ((n/d : ℕ) : ℝ)/(n : ℝ)-(((n-1)/(2*d) : ℕ) : ℝ)/(n : ℝ) := by
    rw [Ioc_filter_dvd_card,Nat.cast_sub (Nat.div_le_div_right (show (n-1)/2 ≤ n from (Nat.div_le_self _ _).trans (Nat.sub_le _ _))),sub_div]
    simp only [Nat.div_div_eq_div_mul]
  simp_rw [heq]
  convert h using 1
  by_cases hd : d = 0
  · simp [hd]
  · have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    push_cast
    field_simp
    ring

end
end Paper14
