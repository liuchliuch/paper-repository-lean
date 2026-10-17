import CalibrationDistance.Lower
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Prod

/-! One-step lower-bound identities for arbitrary forecast probability laws.
There is no finite-support restriction on the forecaster in these lemmas. -/

open MeasureTheory

namespace CalibrationDistance

variable {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω} [IsProbabilityMeasure ν]

theorem lower_integrable_unit {P : Ω → ℝ} (hP : AEMeasurable P ν)
    (hunit : ∀ᵐ ω ∂ν, P ω ∈ Set.Icc (0 : ℝ) 1) : Integrable P ν := by
  apply (integrable_const (1 : ℝ)).mono' hP.aestronglyMeasurable
  filter_upwards [hunit] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg hω.1]
  exact hω.2

theorem lower_mean_mem_unit {P : Ω → ℝ} (hP : AEMeasurable P ν)
    (hunit : ∀ᵐ ω ∂ν, P ω ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, P ω ∂ν) ∈ Set.Icc (0 : ℝ) 1 := by
  have hp := lower_integrable_unit hP hunit
  constructor
  · exact integral_nonneg_of_ae (hunit.mono fun _ h => h.1)
  · calc
      ∫ ω, P ω ∂ν ≤ ∫ _ : Ω, (1 : ℝ) ∂ν :=
        integral_mono_ae hp (integrable_const 1) (hunit.mono fun _ h => h.2)
      _ = 1 := by simp

theorem lower_integrable_centered_square {P : Ω → ℝ} (hP : AEMeasurable P ν)
    (hunit : ∀ᵐ ω ∂ν, P ω ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => (P ω - ∫ s, P s ∂ν) ^ 2) ν := by
  have hm := lower_mean_mem_unit hP hunit
  apply (integrable_const (1 : ℝ)).mono' ((hP.sub_const _).pow_const 2).aestronglyMeasurable
  filter_upwards [hunit] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have hl : -(1 : ℝ) ≤ P ω - ∫ s, P s ∂ν := by linarith [hω.1, hm.2]
  have hu : P ω - ∫ s, P s ∂ν ≤ 1 := by linarith [hω.2, hm.1]
  nlinarith

/-- The centered forecast has expectation zero under its actual probability law. -/
theorem lower_integral_centered {P : Ω → ℝ} (hP : Integrable P ν) :
    (∫ ω, (P ω - ∫ s, P s ∂ν) ∂ν) = 0 := by
  rw [integral_sub hP (integrable_const _)]
  simp

theorem lower_variance_mem_unit {P : Ω → ℝ} (hP : AEMeasurable P ν)
    (hunit : ∀ᵐ ω ∂ν, P ω ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, (P ω - ∫ s, P s ∂ν) ^ 2 ∂ν) ∈ Set.Icc (0 : ℝ) 1 := by
  have hm := lower_mean_mem_unit hP hunit
  constructor
  · exact integral_nonneg fun _ => sq_nonneg _
  · calc
      (∫ ω, (P ω - ∫ s, P s ∂ν) ^ 2 ∂ν) ≤ ∫ _ : Ω, (1 : ℝ) ∂ν := by
        apply integral_mono_ae (lower_integrable_centered_square hP hunit) (integrable_const 1)
        filter_upwards [hunit] with ω hω
        have hl : -(1 : ℝ) ≤ P ω - ∫ s, P s ∂ν := by linarith [hω.1, hm.2]
        have hu : P ω - ∫ s, P s ∂ν ≤ 1 := by linarith [hω.2, hm.1]
        nlinarith
      _ = 1 := by simp

/-- The conditional energy calculation (5.6), after integrating out the
independent Bernoulli outcome. The mean and variance are actual integrals. -/
theorem lower_step_energy_integral (a : ℕ) {P : Ω → ℝ}
    (hP : AEMeasurable P ν) (hunit : ∀ᵐ ω ∂ν, P ω ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, (1 / 2 - P ω) * (lowerQ a (∫ s, P s ∂ν) - P ω) ∂ν) =
      |(∫ s, P s ∂ν) - 1 / 2| ^ (a + 1) +
        ∫ ω, (P ω - ∫ s, P s ∂ν) ^ 2 ∂ν := by
  have hp := lower_integrable_unit hP hunit
  have hc : Integrable (fun ω => P ω - ∫ s, P s ∂ν) ν :=
    hp.sub (integrable_const (∫ s, P s ∂ν))
  have hv := lower_integrable_centered_square hP hunit
  have heq : (fun ω => (1 / 2 - P ω) * (lowerQ a (∫ s, P s ∂ν) - P ω)) =
      (fun ω => |(∫ s, P s ∂ν) - 1 / 2| ^ (a + 1) +
        (P ω - ∫ s, P s ∂ν) ^ 2 +
        (2 * (∫ s, P s ∂ν) - 1 / 2 - lowerQ a (∫ s, P s ∂ν)) *
          (P ω - ∫ s, P s ∂ν)) := by
    funext ω
    exact lower_energy_expansion a _ _
  have hl : Integrable (fun ω => |(∫ s, P s ∂ν) - 1 / 2| ^ (a + 1) +
      (P ω - ∫ s, P s ∂ν) ^ 2) ν := (integrable_const _).add hv
  have hr : Integrable (fun ω =>
      (2 * (∫ s, P s ∂ν) - 1 / 2 - lowerQ a (∫ s, P s ∂ν)) *
        (P ω - ∫ s, P s ∂ν)) ν := hc.const_mul _
  rw [heq, integral_add hl hr, integral_add (integrable_const _) hv,
    integral_const_mul, lower_integral_centered hp]
  simp

end CalibrationDistance
