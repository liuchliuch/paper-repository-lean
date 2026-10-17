import Paper02.BitSpaceModel
import Paper02.StreamingParameters

/-! Uniform real-polynomial growth of the concrete accuracy, repetition and
binary-register choices. Constants do not depend on dimension or frequencies. -/
noncomputable section
namespace Paper02.ParameterGrowth
open BitSpaceModel StreamingParameters WeightEval

def parameterBudget (d U : ℕ) (ε δ : ℝ) : ℕ :=
  accuracyThreshold ε + (2 * medianHalf δ + 1) +
    registerBits (d + 1) + registerBits (U + 1) + 10

lemma accuracyParameters_one {d U : ℕ} (hd : 1 ≤ d) (hU : 1 ≤ U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    1 ≤ accuracyParameters d U ε δ := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hD := Real.log_nonneg (show (1 : ℝ) ≤ 2 * d by linarith)
  have hU' := Real.log_nonneg (show (1 : ℝ) ≤ 2 * U by linarith)
  have hδ' := log_inverse_nonneg hδ hδ1
  have hi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  unfold accuracyParameters
  linarith

/-- A single quadratic expression in the source's four parameters bounds all
chosen thresholds, repetition counts and logarithmic dimension registers. -/
theorem parameterBudget_bound {d U : ℕ} (hd : 1 ≤ d) (hU : 1 ≤ U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (parameterBudget d U ε δ : ℝ) ≤ 65560 * accuracyParameters d U ε δ ^ 2 := by
  let L := accuracyParameters d U ε δ
  have hL : 1 ≤ L := accuracyParameters_one hd hU hε hε1 hδ hδ1
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hUR : (1 : ℝ) ≤ U := by exact_mod_cast hU
  have hD := Real.log_nonneg (show (1 : ℝ) ≤ 2 * d by linarith)
  have hU' := Real.log_nonneg (show (1 : ℝ) ≤ 2 * U by linarith)
  have hδ' := log_inverse_nonneg hδ hδ1
  have hi : 1 ≤ ε⁻¹ := (one_le_inv₀ hε).2 hε1
  have hiL : ε⁻¹ ≤ L := by dsimp [L, accuracyParameters]; linarith
  have hisq : (ε⁻¹) ^ 2 ≤ L ^ 2 := by nlinarith only [hi, hiL, hL]
  have hK := accuracyThreshold_polynomial hε hε1
  have hR := (median_repetitions_upper hδ hδ1).le
  push_cast at hR
  have hbD := registerBits_log_bound d hd
  have hbU := registerBits_log_bound U hU
  have hsmall : 8 * Real.log (1 / δ) + 2 * Real.log (2 * (d : ℝ)) +
      2 * Real.log (2 * (U : ℝ)) + 15 ≤ 23 * L ^ 2 := by
    have heq : L = ε⁻¹ + Real.log (2 * (d : ℝ)) + Real.log (2 * (U : ℝ)) +
        Real.log (1 / δ) + 1 := rfl
    nlinarith only [heq, hL, hi, hD, hU', hδ']
  unfold parameterBudget
  push_cast
  change _ ≤ 65560 * L ^ 2
  nlinarith only [hK, hR, hbD, hbU, hisq, hsmall]

/-- Raising the actual fourth-degree register bound produces one uniform
polynomial in exactly the four parameters in equation (1.3). -/
theorem fourth_power_bound {d U : ℕ} (hd : 1 ≤ d) (hU : 1 ≤ U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (1024 * (parameterBudget d U ε δ) ^ 4 : ℝ) ≤
      (1024 * 65560 ^ 4 : ℝ) * accuracyParameters d U ε δ ^ 8 := by
  have hb := parameterBudget_bound hd hU hε hε1 hδ hδ1
  have hp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ parameterBudget d U ε δ) hb 4
  calc
    _ ≤ 1024 * (65560 * accuracyParameters d U ε δ ^ 2) ^ 4 :=
      mul_le_mul_of_nonneg_left hp (by norm_num)
    _ = _ := by ring

theorem fourth_power_bound_4096 {d U : ℕ} (hd : 1 ≤ d) (hU : 1 ≤ U)
    {ε δ : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    (4096 * (parameterBudget d U ε δ) ^ 4 : ℝ) ≤
      (4096 * 65560 ^ 4 : ℝ) * accuracyParameters d U ε δ ^ 8 := by
  have h := fourth_power_bound hd hU hε hε1 hδ hδ1
  nlinarith only [h]

end Paper02.ParameterGrowth
