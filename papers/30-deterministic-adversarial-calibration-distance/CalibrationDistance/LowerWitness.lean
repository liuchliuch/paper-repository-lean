import CalibrationDistance.Core
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Tactic

/-! Integral forms of the genuine calibration-distance witnesses from Lemma 4.1.
These apply to arbitrary probability laws, including continuous forecast laws.
Integrability of the loss is a technical hypothesis here; ProtocolLoss proves it
for the actual finite-horizon law. -/

open MeasureTheory
open scoped BigOperators

namespace CalibrationDistance

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {ν : Measure Ω} [IsFiniteMeasure ν]

noncomputable def lowerLinearWitness (P Y : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, (1 / 2 - P ω i) * (Y ω i - P ω i)

noncomputable def lowerTotalResidual (P Y : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, (Y ω i - P ω i)

theorem integrable_lowerLinearWitness {P Y : Ω → ι → ℝ}
    (hP : ∀ i, AEMeasurable (fun ω => P ω i) ν)
    (hY : ∀ i, AEMeasurable (fun ω => Y ω i) ν)
    (hp : ∀ᵐ ω ∂ν, Valid (P ω)) (hy : ∀ᵐ ω ∂ν, Valid (Y ω)) :
    Integrable (lowerLinearWitness P Y) ν := by
  have hm : AEMeasurable (lowerLinearWitness P Y) ν := by
    exact Finset.aemeasurable_fun_sum _ (fun i _ =>
      (aemeasurable_const.sub (hP i)).mul ((hY i).sub (hP i)))
  apply (integrable_const (Fintype.card ι : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [hp, hy] with ω hpω hyω
  rw [Real.norm_eq_abs]
  calc
    |lowerLinearWitness P Y ω| ≤
        ∑ i, |(1 / 2 - P ω i) * (Y ω i - P ω i)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hc : |1 / 2 - P ω i| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hpω i).1, (hpω i).2]
      simpa using mul_le_mul hc (abs_outcome_sub_le_one hpω hyω i)
        (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = Fintype.card ι := by simp

theorem integrable_lowerTotalResidual {P Y : Ω → ι → ℝ}
    (hP : ∀ i, AEMeasurable (fun ω => P ω i) ν)
    (hY : ∀ i, AEMeasurable (fun ω => Y ω i) ν)
    (hp : ∀ᵐ ω ∂ν, Valid (P ω)) (hy : ∀ᵐ ω ∂ν, Valid (Y ω)) :
    Integrable (lowerTotalResidual P Y) ν := by
  have hm : AEMeasurable (lowerTotalResidual P Y) ν := by
    exact Finset.aemeasurable_fun_sum _ (fun i _ => (hY i).sub (hP i))
  apply (integrable_const (Fintype.card ι : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [hp, hy] with ω hpω hyω
  rw [Real.norm_eq_abs]
  calc
    |lowerTotalResidual P Y ω| ≤ ∑ i, |Y ω i - P ω i| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : ι, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => abs_outcome_sub_le_one hpω hyω i)
    _ = Fintype.card ι := by simp

/-- The first inequality in (5.7), integrated under an actual law. -/
theorem integral_linear_witness_abs_le {P Y : Ω → ι → ℝ}
    (hP : ∀ i, AEMeasurable (fun ω => P ω i) ν)
    (hY : ∀ i, AEMeasurable (fun ω => Y ω i) ν)
    (hp : ∀ᵐ ω ∂ν, Valid (P ω)) (hy : ∀ᵐ ω ∂ν, Valid (Y ω))
    (hL : Integrable (fun ω => calDist (P ω) (Y ω)) ν) :
    (2 / 3 : ℝ) * (∫ ω, |lowerLinearWitness P Y ω| ∂ν) ≤
      ∫ ω, calDist (P ω) (Y ω) ∂ν := by
  rw [← integral_const_mul]
  apply integral_mono_ae ((integrable_lowerLinearWitness hP hY hp hy).abs.const_mul _) hL
  filter_upwards [hp, hy] with ω hpω hyω
  exact linear_witness_le_calDist hpω hyω

/-- Jensen and the witness comparison in (5.7). The energy identity itself
must still be proved from the actual auxiliary transition law. -/
theorem integral_linear_witness_le {P Y : Ω → ι → ℝ}
    (hP : ∀ i, AEMeasurable (fun ω => P ω i) ν)
    (hY : ∀ i, AEMeasurable (fun ω => Y ω i) ν)
    (hp : ∀ᵐ ω ∂ν, Valid (P ω)) (hy : ∀ᵐ ω ∂ν, Valid (Y ω))
    (hL : Integrable (fun ω => calDist (P ω) (Y ω)) ν) :
    (2 / 3 : ℝ) * (∫ ω, lowerLinearWitness P Y ω ∂ν) ≤
      ∫ ω, calDist (P ω) (Y ω) ∂ν := by
  have hi : (∫ ω, lowerLinearWitness P Y ω ∂ν) ≤
      ∫ ω, |lowerLinearWitness P Y ω| ∂ν :=
    integral_mono (integrable_lowerLinearWitness hP hY hp hy)
      (integrable_lowerLinearWitness hP hY hp hy).abs (fun _ => le_abs_self _)
  exact (mul_le_mul_of_nonneg_left hi (by norm_num)).trans
    (integral_linear_witness_abs_le hP hY hp hy hL)

/-- The total-residual comparison (4.2), integrated under an actual law. -/
theorem integral_total_residual_le {P Y : Ω → ι → ℝ}
    (hP : ∀ i, AEMeasurable (fun ω => P ω i) ν)
    (hY : ∀ i, AEMeasurable (fun ω => Y ω i) ν)
    (hp : ∀ᵐ ω ∂ν, Valid (P ω)) (hy : ∀ᵐ ω ∂ν, Valid (Y ω))
    (hL : Integrable (fun ω => calDist (P ω) (Y ω)) ν) :
    (∫ ω, |lowerTotalResidual P Y ω| ∂ν) ≤
      ∫ ω, calDist (P ω) (Y ω) ∂ν := by
  apply integral_mono_ae (integrable_lowerTotalResidual hP hY hp hy).abs hL
  filter_upwards [hp, hy] with ω hpω hyω
  exact total_residual_le_calDist hpω hyω

/-- The reverse triangle step in (5.17)/(5.21). Only a pathwise residual
decomposition is needed here; moment and drift bounds are not hypotheses. -/
theorem integral_residual_difference_le {P Y : Ω → ι → ℝ} {Z D : Ω → ℝ}
    (hp : ∀ᵐ ω ∂ν, Valid (P ω)) (hy : ∀ᵐ ω ∂ν, Valid (Y ω))
    (hZ : Integrable Z ν) (hD : Integrable D ν)
    (hL : Integrable (fun ω => calDist (P ω) (Y ω)) ν)
    (hres : ∀ᵐ ω ∂ν, lowerTotalResidual P Y ω = Z ω - D ω) :
    (∫ ω, |Z ω| ∂ν) - (∫ ω, |D ω| ∂ν) ≤
      ∫ ω, calDist (P ω) (Y ω) ∂ν := by
  rw [← integral_sub hZ.abs hD.abs]
  apply integral_mono_ae (hZ.abs.sub hD.abs) hL
  filter_upwards [hp, hy, hres] with ω hpω hyω hresω
  calc
    |Z ω| - |D ω| ≤ |Z ω - D ω| := abs_sub_abs_le_abs_sub _ _
    _ = |lowerTotalResidual P Y ω| := by rw [hresω]
    _ ≤ calDist (P ω) (Y ω) := total_residual_le_calDist hpω hyω

end CalibrationDistance
