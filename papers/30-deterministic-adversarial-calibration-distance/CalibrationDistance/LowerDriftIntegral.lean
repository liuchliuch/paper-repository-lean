import CalibrationDistance.Lower
import CalibrationDistance.LowerScale
import CalibrationDistance.Moments

/-! The complete drift calculation (A.5), for the actual mean and variance
arrays of any probability process. All integrability obligations are derived
from the unit-interval bounds on those arrays. -/

open MeasureTheory
open scoped BigOperators

namespace CalibrationDistance

variable {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
variable {ν : Measure Ω} [IsProbabilityMeasure ν]

noncomputable def lowerEnergy (a : ℕ) (μ v : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, (|μ ω i - 1 / 2| ^ (a + 1) + v ω i)

noncomputable def lowerDriftTotal (a : ℕ) (μ : Ω → ι → ℝ) (ω : Ω) : ℝ :=
  ∑ i, lowerDrift a (μ ω i)

theorem lowerEnergy_nonneg (a : ℕ) {μ v : Ω → ι → ℝ}
    (hv : ∀ ω i, 0 ≤ v ω i) (ω : Ω) : 0 ≤ lowerEnergy a μ v ω := by
  exact Finset.sum_nonneg (fun i _ => add_nonneg (pow_nonneg (abs_nonneg _) _) (hv ω i))

theorem lowerEnergy_le_card (a : ℕ) {μ v : Ω → ι → ℝ}
    (hμ : ∀ ω i, μ ω i ∈ Set.Icc (0 : ℝ) 1)
    (hv : ∀ ω i, v ω i ≤ 1) (ω : Ω) :
    lowerEnergy a μ v ω ≤ 2 * Fintype.card ι := by
  calc
    lowerEnergy a μ v ω ≤ ∑ _i : ι, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have he : |μ ω i - 1 / 2| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [(hμ ω i).1, (hμ ω i).2]
      have hp := pow_le_one₀ (abs_nonneg (μ ω i - 1 / 2)) he (n := a + 1)
      linarith [hv ω i]
    _ = 2 * Fintype.card ι := by simp; ring

theorem aemeasurable_lowerEnergy (a : ℕ) {μ v : Ω → ι → ℝ}
    (hμ : ∀ i, AEMeasurable (fun ω => μ ω i) ν)
    (hv : ∀ i, AEMeasurable (fun ω => v ω i) ν) :
    AEMeasurable (lowerEnergy a μ v) ν := by
  exact Finset.aemeasurable_fun_sum _ (fun i _ =>
    (((hμ i).sub_const (1 / 2 : ℝ)).abs.pow_const (a + 1)).add (hv i))

theorem integrable_lowerEnergy (a : ℕ) {μ v : Ω → ι → ℝ}
    (hμ : ∀ i, AEMeasurable (fun ω => μ ω i) ν)
    (hv : ∀ i, AEMeasurable (fun ω => v ω i) ν)
    (hμb : ∀ ω i, μ ω i ∈ Set.Icc (0 : ℝ) 1)
    (hvb : ∀ ω i, v ω i ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (lowerEnergy a μ v) ν := by
  apply (integrable_const (2 * Fintype.card ι : ℝ)).mono'
    (aemeasurable_lowerEnergy a hμ hv).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (lowerEnergy_nonneg a (fun ω i => (hvb ω i).1) ω)]
    exact lowerEnergy_le_card a hμb (fun ω i => (hvb ω i).2) ω

theorem integrable_lowerEnergy_rpow {a : ℕ} {μ v : Ω → ι → ℝ} {r : ℝ} (hr : 0 ≤ r)
    (hμ : ∀ i, AEMeasurable (fun ω => μ ω i) ν)
    (hv : ∀ i, AEMeasurable (fun ω => v ω i) ν)
    (hμb : ∀ ω i, μ ω i ∈ Set.Icc (0 : ℝ) 1)
    (hvb : ∀ ω i, v ω i ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun ω => lowerEnergy a μ v ω ^ r) ν := by
  apply (integrable_const ((2 * Fintype.card ι : ℝ) ^ r)).mono'
    ((aemeasurable_lowerEnergy a hμ hv).pow_const r).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    have hn := lowerEnergy_nonneg (μ := μ) a (fun ω i => (hvb ω i).1) ω
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hn r)]
    exact Real.rpow_le_rpow hn (lowerEnergy_le_card a hμb (fun ω i => (hvb ω i).2) ω) hr

theorem integrable_lowerDriftTotal {a : ℕ} (ha : 1 ≤ a) {μ : Ω → ι → ℝ}
    (hμ : ∀ i, AEMeasurable (fun ω => μ ω i) ν)
    (hμb : ∀ ω i, μ ω i ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (lowerDriftTotal a μ) ν := by
  have hm : AEMeasurable (lowerDriftTotal a μ) ν := by
    exact Finset.aemeasurable_fun_sum _ (fun i _ =>
      (continuous_lowerDrift ha).measurable.comp_aemeasurable (hμ i))
  apply (integrable_const (Fintype.card ι : ℝ)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]
    calc
      |lowerDriftTotal a μ ω| ≤ ∑ i, |lowerDrift a (μ ω i)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : ι, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_lowerDrift a ha]
        apply pow_le_one₀ (abs_nonneg _)
        rw [abs_le]
        constructor <;> linarith [(hμb ω i).1, (hμb ω i).2]
      _ = Fintype.card ι := by simp

/-- The integral Hölder/Jensen step of (A.5) specialized to the paper's
literal drift and energy, including integrability rather than assuming it. -/
theorem lower_drift_integral_holder {a : ℕ} (ha : 1 ≤ a) {μ v : Ω → ι → ℝ}
    (hμ : ∀ i, AEMeasurable (fun ω => μ ω i) ν)
    (hv : ∀ i, AEMeasurable (fun ω => v ω i) ν)
    (hμb : ∀ ω i, μ ω i ∈ Set.Icc (0 : ℝ) 1)
    (hvb : ∀ ω i, v ω i ∈ Set.Icc (0 : ℝ) 1) :
    (∫ ω, |lowerDriftTotal a μ ω| ∂ν) ≤
      (Fintype.card ι : ℝ) ^ (1 / ((a : ℝ) + 1)) *
        (∫ ω, lowerEnergy a μ v ω ∂ν) ^ ((a : ℝ) / (a + 1)) := by
  have haa : (0 : ℝ) < a := by exact_mod_cast (by omega : 0 < a)
  have hd : ∀ᵐ ω ∂ν, ∀ i ∈ (Finset.univ : Finset ι),
      |lowerDrift a (μ ω i)| ≤ |μ ω i - 1 / 2| ^ (a : ℝ) := by
    exact Filter.Eventually.of_forall fun ω i _ => by
      simp only [Real.rpow_natCast]
      exact (abs_lowerDrift a ha (μ ω i)).le
  have he : ∀ᵐ ω ∂ν, (∑ i ∈ (Finset.univ : Finset ι),
      |μ ω i - 1 / 2| ^ ((a : ℝ) + 1)) ≤ lowerEnergy a μ v ω := by
    exact Filter.Eventually.of_forall fun ω => by
      rw [show ((a : ℝ) + 1) = ((a + 1 : ℕ) : ℝ) by norm_num]
      simp only [Real.rpow_natCast]
      unfold lowerEnergy
      apply Finset.sum_le_sum
      intro i _
      linarith [(hvb ω i).1]
  have h := drift_integral_le (μ := ν) Finset.univ
    (fun i ω => μ ω i - 1 / 2) (fun i ω => lowerDrift a (μ ω i))
    (lowerEnergy a μ v) haa hd he
    (Filter.Eventually.of_forall (lowerEnergy_nonneg a (fun ω i => (hvb ω i).1)))
    (by simpa [lowerDriftTotal] using (integrable_lowerDriftTotal ha hμ hμb).abs)
    (integrable_lowerEnergy a hμ hv hμb hvb)
    (integrable_lowerEnergy_rpow (by positivity) hμ hv hμb hvb)
  simpa only [Finset.card_univ, lowerDriftTotal] using h

/-- The complete small-energy drift estimate (A.5), including the scale
identity. This applies directly to realized conditional means and variances. -/
theorem lower_drift_integral_bound {a : ℕ} (ha : 1 ≤ a) {μ v : Ω → ι → ℝ}
    (hμ : ∀ i, AEMeasurable (fun ω => μ ω i) ν)
    (hv : ∀ i, AEMeasurable (fun ω => v ω i) ν)
    (hμb : ∀ ω i, μ ω i ∈ Set.Icc (0 : ℝ) 1)
    (hvb : ∀ ω i, v ω i ∈ Set.Icc (0 : ℝ) 1)
    (hcard : 0 < Fintype.card ι) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hsmall : (∫ ω, lowerEnergy a μ v ω ∂ν) ≤
      c * lowerScale (Fintype.card ι) a) :
    (∫ ω, |lowerDriftTotal a μ ω| ∂ν) ≤
      Real.sqrt c * Real.sqrt (Fintype.card ι) := by
  apply lowerScale_drift_bound (by exact_mod_cast hcard) ha hc0 hc1
    (integral_nonneg (lowerEnergy_nonneg a (fun ω i => (hvb ω i).1))) hsmall
  exact lower_drift_integral_holder ha hμ hv hμb hvb

end CalibrationDistance
