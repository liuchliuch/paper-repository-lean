import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Tactic

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter

namespace CalibrationDistance

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The two-sided exponential tail obtained from the mgf, with no support restriction. -/
theorem abs_tail_le_of_subgaussian [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) {u : ℝ} (hu : 0 ≤ u) :
    μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-u ^ 2 / (2 * c)) := by
  have hs : {ω | u ≤ |X ω|} = {ω | u ≤ X ω} ∪ {ω | u ≤ -X ω} := by
    ext ω
    simp only [Set.mem_setOf_eq, Set.mem_union, le_abs]
  rw [hs]
  calc
    μ.real ({ω | u ≤ X ω} ∪ {ω | u ≤ -X ω}) ≤
        μ.real {ω | u ≤ X ω} + μ.real {ω | u ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-u ^ 2 / (2 * c)) + Real.exp (-u ^ 2 / (2 * c)) :=
      add_le_add (hX.measure_ge_le hu) (hX.neg.measure_ge_le hu)
    _ = _ := by ring

/-- Exact tail integral used in (A.4). -/
theorem gaussian_fourth_tail_integral {b : ℝ} (hb : 0 < b) :
    (∫ u in Set.Ioi (0 : ℝ), u ^ (3 : ℝ) * Real.exp (-b * u ^ (2 : ℝ))) =
      1 / (2 * b ^ 2) := by
  rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (-1 : ℝ) < 3) hb]
  norm_num only [show -((3 : ℝ) + 1) / 2 = -2 by norm_num,
    show ((3 : ℝ) + 1) / 2 = 2 by norm_num]
  have hgamma : Real.Gamma 2 = 1 := by
    simp [← Real.Gamma_nat_eq_factorial 1]
  rw [hgamma, mul_one, Real.rpow_neg hb.le, Real.rpow_ofNat]
  field_simp

/-- Layer-cake integration gives the sharp fourth-moment constant used in the paper. -/
theorem fourth_moment_le_of_tail [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) (h4 : Integrable (fun ω => X ω ^ 4) μ)
    {b : ℝ} (hb : 0 < b)
    (htail : ∀ u, 0 ≤ u → μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-b * u ^ 2)) :
    (∫ ω, X ω ^ 4 ∂μ) ≤ 4 / b ^ 2 := by
  have h4n : ∀ᵐ ω ∂μ, 0 ≤ X ω ^ 4 := Eventually.of_forall (fun _ => by positivity)
  apply (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 4 / b ^ 2)).mp
  rw [ofReal_integral_eq_lintegral_ofReal h4 h4n]
  have heq : (fun ω => ENNReal.ofReal (X ω ^ 4)) =
      (fun ω => ENNReal.ofReal (|X ω| ^ (4 : ℝ))) := by
    funext ω
    congr 1
    norm_num only [Real.rpow_ofNat]
    rw [← abs_pow]
    exact (abs_of_nonneg (by positivity)).symm
  rw [heq, lintegral_rpow_eq_lintegral_meas_le_mul μ
    (Eventually.of_forall fun ω => abs_nonneg (X ω)) hX.abs (by norm_num : (0 : ℝ) < 4)]
  have hbound :
      (∫⁻ u in Set.Ioi (0 : ℝ), μ {ω | u ≤ |X ω|} * ENNReal.ofReal (u ^ ((4 : ℝ) - 1))) ≤
      ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (2 * Real.exp (-b * u ^ 2) * u ^ (3 : ℝ)) := by
    apply setLIntegral_mono' measurableSet_Ioi
    intro u hu
    have hμ : μ {ω | u ≤ |X ω|} ≤ ENNReal.ofReal (2 * Real.exp (-b * u ^ 2)) := by
      rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
      exact ENNReal.ofReal_le_ofReal (htail u hu.le)
    norm_num only [show (4 : ℝ) - 1 = 3 by norm_num]
    rw [ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * Real.exp (-b * u ^ 2))]
    exact mul_le_mul_right' hμ _
  apply le_trans (mul_le_mul_left' hbound (ENNReal.ofReal 4))
  have hi : IntegrableOn (fun u : ℝ => 2 * Real.exp (-b * u ^ 2) * u ^ (3 : ℝ))
      (Set.Ioi 0) volume := by
    have hi := (integrableOn_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 3)).const_mul 2
    change Integrable _ (volume.restrict (Set.Ioi 0))
    convert hi using 1
    funext u
    ring
  have hinn : ∀ᵐ u ∂volume.restrict (Set.Ioi 0),
      0 ≤ 2 * Real.exp (-b * u ^ 2) * u ^ (3 : ℝ) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : 0 ≤ u := hu.le
    positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hi hinn, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
  apply ENNReal.ofReal_le_ofReal
  have hi_eq : (∫ u in Set.Ioi (0 : ℝ), 2 * Real.exp (-b * u ^ 2) * u ^ (3 : ℝ)) =
      2 * (1 / (2 * b ^ 2)) := by
    rw [← gaussian_fourth_tail_integral hb, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro u hu
    dsimp only
    simp only [Real.rpow_ofNat]
    ring
  rw [hi_eq]
  field_simp
  norm_num

/-- A sub-Gaussian variance proxy `c` implies `E X⁴ ≤ 16 c²`. -/
theorem fourth_moment_le_of_subgaussian [IsProbabilityMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (hX : HasSubgaussianMGF X c μ) (hc : 0 < c) :
    (∫ ω, X ω ^ 4 ∂μ) ≤ 16 * (c : ℝ) ^ 2 := by
  have hc' : 0 < (c : ℝ) := hc
  have h4 := ProbabilityTheory.integrable_pow_of_integrable_exp_mul (X := X)
    (by norm_num : (1 : ℝ) ≠ 0) (hX.integrable_exp_mul 1) (by simpa using hX.integrable_exp_mul (-1)) 4
  have htail (u : ℝ) (hu : 0 ≤ u) :
      μ.real {ω | u ≤ |X ω|} ≤ 2 * Real.exp (-(1 / (2 * (c : ℝ))) * u ^ 2) := by
    have h := abs_tail_le_of_subgaussian hX hu
    convert h using 1
    congr 2
    field_simp
  have h := fourth_moment_le_of_tail hX.aemeasurable h4
    (by positivity : 0 < 1 / (2 * (c : ℝ))) htail
  convert h using 1
  field_simp
  ring

/-- Hoeffding's lemma for one centered summand supported in an interval of length one. -/
theorem centered_unit_interval_subgaussian [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {l : ℝ}
    (hbound : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc l (l + 1)) (hmean : ∫ ω, X ω ∂μ = 0) :
    HasSubgaussianMGF X (1 / 4 : ℝ≥0) μ := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero hX hbound hmean
  have heq : l + 1 - l = (1 : ℝ) := by ring
  norm_num [heq] at h ⊢
  exact h

/-- Independence of the outcome and current forecast gives the proxy `1/2` in (A.3). -/
theorem two_centered_unit_interval_subgaussian [IsProbabilityMeasure μ] {X Y : Ω → ℝ}
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) {lX lY : ℝ}
    (hbX : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc lX (lX + 1))
    (hbY : ∀ᵐ ω ∂μ, Y ω ∈ Set.Icc lY (lY + 1))
    (hmX : ∫ ω, X ω ∂μ = 0) (hmY : ∫ ω, Y ω ∂μ = 0)
    (hindep : IndepFun X Y μ) :
    HasSubgaussianMGF (fun ω => X ω + Y ω) (1 / 2 : ℝ≥0) μ := by
  have h := (centered_unit_interval_subgaussian hX hbX hmX).add_of_indepFun
    (centered_unit_interval_subgaussian hY hbY hmY) hindep
  norm_num at h ⊢
  exact h

/-- Azuma-Hoeffding iteration followed by the exact layer-cake calculation. -/
theorem martingale_sum_fourth_moment [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›} {c : ℝ≥0}
    (hc : 0 < c) (h_adapted : Adapted ℱ Y)
    (h0 : HasSubgaussianMGF (Y 0) c μ) (n : ℕ) (hn : 0 < n)
    (h_subG : ∀ i < n - 1, HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) c μ) :
    (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 4 ∂μ) ≤ 16 * (n : ℝ) ^ 2 * (c : ℝ) ^ 2 := by
  have hsum := HasSubgaussianMGF_sum_of_HasCondSubgaussianMGF
    (cY := fun _ => c) h_adapted h0 n h_subG
  have hc_sum : 0 < ∑ _i ∈ Finset.range n, c := by
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    exact mul_pos (Nat.cast_pos.mpr hn) hc
  have h := fourth_moment_le_of_subgaussian hsum hc_sum
  simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    NNReal.coe_mul, NNReal.coe_natCast, mul_pow, mul_assoc] using h

/-- Randomized lower-bound fourth moment, equation (A.4). -/
theorem randomized_martingale_fourth_moment [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    (h_adapted : Adapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (1 / 2) μ)
    (n : ℕ) (hn : 0 < n)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (1 / 2) μ) :
    (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 4 ∂μ) ≤ 4 * (n : ℝ) ^ 2 := by
  have h := martingale_sum_fourth_moment (by norm_num : (0 : ℝ≥0) < 1 / 2)
    h_adapted h0 n hn h_subG
  norm_num at h ⊢
  nlinarith

/-- Deterministic-forecaster fourth moment, equation (5.20) and Appendix A.3. -/
theorem deterministic_martingale_fourth_moment [StandardBorelSpace Ω] [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {ℱ : Filtration ℕ ‹MeasurableSpace Ω›}
    (h_adapted : Adapted ℱ Y) (h0 : HasSubgaussianMGF (Y 0) (1 / 4) μ)
    (n : ℕ) (hn : 0 < n)
    (h_subG : ∀ i < n - 1,
      HasCondSubgaussianMGF (ℱ i) (ℱ.le i) (Y (i + 1)) (1 / 4) μ) :
    (∫ ω, (∑ i ∈ Finset.range n, Y i ω) ^ 4 ∂μ) ≤ (n : ℝ) ^ 2 := by
  have h := martingale_sum_fourth_moment (by norm_num : (0 : ℝ≥0) < 1 / 4)
    h_adapted h0 n hn h_subG
  norm_num at h ⊢
  nlinarith

end CalibrationDistance
