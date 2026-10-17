import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Fisher information and the volume of a concentration set

The Hölder step in the proof of Lemma 3.1 is proved for actual measures and
measurable functions below. The Sobolev consequence is proved for compactly
supported C¹ real functions on Euclidean space using mathlib's Gagliardo–Nirenberg–
Sobolev theorem. Its constant is the explicit mathlib Sobolev constant, depending
on the dimension. This does **not** establish the paper's constant `1 / n`, nor
the extension from C¹ to weakly differentiable H¹ square roots.
-/

noncomputable section
open scoped ENNReal NNReal
open MeasureTheory Set

namespace Paper26.FisherVolume

/-- The mass of the density `|h|²` in a measurable region (the extended
nonnegative integral also makes sense for arbitrary sets). -/
def rootMass {E : Type*} [MeasurableSpace E] (μ : Measure E) (h : E → ℝ)
    (s : Set E) : ℝ≥0∞ := ∫⁻ x in s, ‖h x‖ₑ ^ (2 : ℕ) ∂μ

/-- The integrand is exactly the real squared-root density. -/
theorem rootMass_eq_lintegral_sq {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (h : E → ℝ) (s : Set E) :
    rootMass μ h s = ∫⁻ x in s, ENNReal.ofReal (h x ^ (2 : ℕ)) ∂μ := by
  unfold rootMass
  apply lintegral_congr
  intro x
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2, sq_abs]

/-- Root-gradient formulation of the Fisher information from Section 3.1.
For a scalar function on Euclidean space the derivative's operator norm is the
Euclidean norm of its gradient. -/
def rootFisher {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] (μ : Measure E) (h : E → ℝ) : ℝ≥0∞ :=
  4 * ∫⁻ x, ‖fderiv ℝ h x‖ₑ ^ (2 : ℕ) ∂μ

/-- Hölder's concentration estimate. It is an actual integral bound and does not
assume any Sobolev or Fisher-information conclusion. -/
theorem rootMass_le_measure_mul_eLpNorm_sq
    {E : Type*} [MeasurableSpace E] (μ : Measure E) {h : E → ℝ}
    (hh : AEStronglyMeasurable h μ) (s : Set E) {q : ℝ≥0}
    (hq : (2 : ℝ≥0) ≤ q) :
    rootMass μ h s ≤ μ s ^ (1 - 2 / (q : ℝ)) * eLpNorm h q μ ^ (2 : ℕ) := by
  have hlp := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
    (show (2 : ℝ≥0∞) ≤ (q : ℝ≥0∞) by exact_mod_cast hq)
    (hh.mono_measure Measure.restrict_le_self : AEStronglyMeasurable h (μ.restrict s))
  have hmass : rootMass μ h s = eLpNorm h 2 (μ.restrict s) ^ (2 : ℕ) := by
    unfold rootMass
    simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
      (eLpNorm_nnreal_pow_eq_lintegral (μ := μ.restrict s) (f := h)
        (p := (2 : ℝ≥0)) (by norm_num)).symm
  rw [hmass]
  calc
    eLpNorm h 2 (μ.restrict s) ^ (2 : ℕ)
        ≤ (eLpNorm h q (μ.restrict s) *
          μ s ^ (1 / (2 : ℝ) - 1 / (q : ℝ))) ^ (2 : ℕ) := by
      simpa using pow_le_pow_left' hlp 2
    _ = μ s ^ (1 - 2 / (q : ℝ)) *
          eLpNorm h q (μ.restrict s) ^ (2 : ℕ) := by
      rw [mul_pow]
      have hpow : (μ s ^ (1 / (2 : ℝ) - 1 / (q : ℝ))) ^ (2 : ℕ) =
          μ s ^ (1 - 2 / (q : ℝ)) := by
        rw [← ENNReal.rpow_two, ← ENNReal.rpow_mul]
        congr 1
        ring
      rw [hpow, mul_comm]
    _ ≤ μ s ^ (1 - 2 / (q : ℝ)) * eLpNorm h q μ ^ (2 : ℕ) := by
      exact mul_le_mul_left' (pow_le_pow_left' (eLpNorm_restrict_le h q μ s) 2) _

/-- The Sobolev critical exponent for the squared-gradient energy. -/
def criticalExponent (n : ℕ) : ℝ≥0 := ((2 : ℝ≥0)⁻¹ - (n : ℝ≥0)⁻¹)⁻¹

theorem criticalExponent_inv {n : ℕ} (hn : 3 ≤ n) :
    ((criticalExponent n : ℝ≥0) : ℝ)⁻¹ = (2 : ℝ)⁻¹ - (n : ℝ)⁻¹ := by
  have hn' : (2 : ℝ≥0) < n := by exact_mod_cast (by omega : 2 < n)
  simp only [criticalExponent, NNReal.coe_inv, inv_inv]
  rw [NNReal.coe_sub]
  · simp
  · exact le_of_lt (inv_lt_inv₀ (by positivity) (by positivity) |>.2 hn')

theorem two_le_criticalExponent {n : ℕ} (hn : 3 ≤ n) :
    (2 : ℝ≥0) ≤ criticalExponent n := by
  have hn' : (2 : ℝ≥0) < n := by exact_mod_cast (by omega : 2 < n)
  have hdiff : 0 < (2 : ℝ≥0)⁻¹ - (n : ℝ≥0)⁻¹ := by
    exact tsub_pos_iff_lt.mpr ((inv_lt_inv₀ (by positivity) (by positivity)).2 hn')
  unfold criticalExponent
  rw [le_inv_comm₀ (by norm_num) hdiff]
  exact tsub_le_self

/-- The real scalar Sobolev constant supplied by mathlib, with derivative
exponent two and Lebesgue measure on `ℝⁿ`. -/
def smoothSobolevConstant (n : ℕ) : ℝ≥0 :=
  eLpNormLESNormFDerivOfEqInnerConst
    (volume : Measure (EuclideanSpace ℝ (Fin n))) 2

/-- A genuine Lebesgue Fisher-volume estimate for compactly supported C¹ square
roots. The dimension-dependent constant is mathlib's Sobolev constant; the
stronger explicit coefficient in the paper is not asserted here. -/
theorem rootMass_le_smoothSobolev_energy {n : ℕ} (hn : 3 ≤ n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (s : Set (EuclideanSpace ℝ (Fin n))) :
    rootMass volume h s ≤ volume s ^ (2 / (n : ℝ)) *
      (smoothSobolevConstant n : ℝ≥0∞) ^ (2 : ℕ) *
        ∫⁻ x, ‖fderiv ℝ h x‖ₑ ^ (2 : ℕ) := by
  have hq := criticalExponent_inv hn
  have hs := eLpNorm_le_eLpNorm_fderiv_of_eq_inner
    (volume : Measure (EuclideanSpace ℝ (Fin n))) hh hc
    (p := (2 : ℝ≥0)) (p' := criticalExponent n) (by norm_num)
    (by simpa using (show 0 < n by omega)) (by simpa using hq)
  have hexp : 1 - 2 / (criticalExponent n : ℝ) = 2 / (n : ℝ) := by
    rw [div_eq_mul_inv, hq]
    ring
  calc
    rootMass volume h s ≤ volume s ^ (1 - 2 / (criticalExponent n : ℝ)) *
        eLpNorm h (criticalExponent n) volume ^ (2 : ℕ) :=
      rootMass_le_measure_mul_eLpNorm_sq volume hh.continuous.aestronglyMeasurable s
        (two_le_criticalExponent hn)
    _ ≤ volume s ^ (2 / (n : ℝ)) *
        ((smoothSobolevConstant n : ℝ≥0∞) * eLpNorm (fderiv ℝ h) 2 volume) ^ (2 : ℕ) := by
      rw [hexp]
      gcongr
      exact hs
    _ = volume s ^ (2 / (n : ℝ)) *
        (smoothSobolevConstant n : ℝ≥0∞) ^ (2 : ℕ) *
          ∫⁻ x, ‖fderiv ℝ h x‖ₑ ^ (2 : ℕ) := by
      have henergy : eLpNorm (fderiv ℝ h) 2 volume ^ (2 : ℕ) =
          ∫⁻ x, ‖fderiv ℝ h x‖ₑ ^ (2 : ℕ) := by
        simpa only [ENNReal.coe_ofNat, NNReal.coe_ofNat, ENNReal.rpow_two] using
          (eLpNorm_nnreal_pow_eq_lintegral (μ := volume) (f := fderiv ℝ h)
            (p := (2 : ℝ≥0)) (by norm_num))
      rw [mul_pow, henergy, mul_assoc]

/-- The preceding estimate, written with the root Fisher information. -/
theorem rootMass_le_smoothFisher {n : ℕ} (hn : 3 ≤ n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (s : Set (EuclideanSpace ℝ (Fin n))) :
    rootMass volume h s ≤ volume s ^ (2 / (n : ℝ)) *
      ((smoothSobolevConstant n : ℝ≥0∞) ^ (2 : ℕ) / 4) * rootFisher volume h := by
  convert rootMass_le_smoothSobolev_energy hn hh hc s using 1
  unfold rootFisher
  simp only [div_eq_mul_inv, mul_assoc]
  rw [ENNReal.inv_mul_cancel_left (by norm_num : (4 : ℝ≥0∞) ≠ 0)
    (by norm_num : (4 : ℝ≥0∞) ≠ ∞)]

/-- The smooth Fisher-volume theorem stated for a nonnegative density `f`
and its actual pointwise square root. -/
theorem densityMass_le_smoothFisher {n : ℕ} (hn : 3 ≤ n)
    {f : EuclideanSpace ℝ (Fin n) → ℝ} (hf : ∀ x, 0 ≤ f x)
    (hh : ContDiff ℝ 1 (fun x => Real.sqrt (f x)))
    (hc : HasCompactSupport (fun x => Real.sqrt (f x)))
    (s : Set (EuclideanSpace ℝ (Fin n))) :
    (∫⁻ x in s, ENNReal.ofReal (f x)) ≤ volume s ^ (2 / (n : ℝ)) *
      ((smoothSobolevConstant n : ℝ≥0∞) ^ (2 : ℕ) / 4) *
        rootFisher volume (fun x => Real.sqrt (f x)) := by
  have hmass : (∫⁻ x in s, ENNReal.ofReal (f x)) =
      rootMass volume (fun x => Real.sqrt (f x)) s := by
    rw [rootMass_eq_lintegral_sq]
    apply lintegral_congr
    intro x
    rw [Real.sq_sqrt (hf x)]
  rw [hmass]
  exact rootMass_le_smoothFisher hn hh hc s

/-- A volume budget can be substituted for the actual success-set volume. -/
theorem rootMass_le_smoothFisher_of_volume_le {n : ℕ} (hn : 3 ≤ n)
    {h : EuclideanSpace ℝ (Fin n) → ℝ} (hh : ContDiff ℝ 1 h)
    (hc : HasCompactSupport h) (s : Set (EuclideanSpace ℝ (Fin n)))
    {v : ℝ≥0∞} (hv : volume s ≤ v) :
    rootMass volume h s ≤ v ^ (2 / (n : ℝ)) *
      ((smoothSobolevConstant n : ℝ≥0∞) ^ (2 : ℕ) / 4) * rootFisher volume h := by
  calc
    rootMass volume h s ≤ volume s ^ (2 / (n : ℝ)) *
        ((smoothSobolevConstant n : ℝ≥0∞) ^ (2 : ℕ) / 4) * rootFisher volume h :=
      rootMass_le_smoothFisher hn hh hc s
    _ ≤ v ^ (2 / (n : ℝ)) *
        ((smoothSobolevConstant n : ℝ≥0∞) ^ (2 : ℕ) / 4) * rootFisher volume h := by
      gcongr

end Paper26.FisherVolume
