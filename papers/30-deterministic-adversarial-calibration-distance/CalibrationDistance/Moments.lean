import Mathlib.Probability.Moments.SubGaussian
import Mathlib.MeasureTheory.Integral.Gamma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Integral
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic

/-!
# Probability and analytic calculations for Appendix A

All integrals in this file are ordinary Bochner integrals on arbitrary measure spaces.
In particular none of these lemmas restrict the forecast law to finite support.
-/

open scoped BigOperators ENNReal NNReal
open MeasureTheory ProbabilityTheory Real Set Filter

namespace CalibrationDistance

section Bounds

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- A bounded nonnegative power is in every Lp on a finite measure space. -/
theorem memLp_abs_rpow_of_bound [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {B r : ℝ} (hr : 0 ≤ r)
    (hB : ∀ᵐ ω ∂μ, |X ω| ≤ B) (p : ℝ≥0∞) :
    MemLp (fun ω => |X ω| ^ r) p μ := by
  apply MemLp.of_bound (hX.abs.pow_const r).aestronglyMeasurable (max B 0 ^ r)
  filter_upwards [hB] with ω hω
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
  exact Real.rpow_le_rpow (abs_nonneg _) (hω.trans (le_max_left _ _)) hr

/-- Hölder interpolation between the first and fourth absolute moments (Appendix A). -/
theorem moment_interpolation_of_bound [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {B : ℝ} (hB : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    (∫ ω, X ω ^ 2 ∂μ) ≤ (∫ ω, |X ω| ∂μ) ^ ((2 : ℝ) / 3) *
      (∫ ω, X ω ^ 4 ∂μ) ^ ((1 : ℝ) / 3) := by
  have hpq : Real.HolderConjugate ((3 : ℝ) / 2) 3 := by
    rw [Real.holderConjugate_iff]; norm_num
  have hf := memLp_abs_rpow_of_bound hX (by norm_num : (0 : ℝ) ≤ 2 / 3) hB
    (ENNReal.ofReal ((3 : ℝ) / 2))
  have hg := memLp_abs_rpow_of_bound hX (by norm_num : (0 : ℝ) ≤ 4 / 3) hB
    (ENNReal.ofReal (3 : ℝ))
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg hpq
    (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg (X ω)) _)
    (Eventually.of_forall fun ω => Real.rpow_nonneg (abs_nonneg (X ω)) _) hf hg
  have hfg : (fun ω => |X ω| ^ ((2 : ℝ) / 3) * |X ω| ^ ((4 : ℝ) / 3)) =
      (fun ω => X ω ^ 2) := by
    funext ω
    rw [← Real.rpow_add_of_nonneg (abs_nonneg _) (by norm_num) (by norm_num)]
    norm_num [sq_abs]
  have hfp : (fun ω => (|X ω| ^ ((2 : ℝ) / 3)) ^ ((3 : ℝ) / 2)) =
      (fun ω => |X ω|) := by
    funext ω
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num
  have hgp : (fun ω => (|X ω| ^ ((4 : ℝ) / 3)) ^ (3 : ℝ)) =
      (fun ω => X ω ^ 4) := by
    funext ω
    rw [← Real.rpow_mul (abs_nonneg _)]
    norm_num only [show ((4 : ℝ) / 3) * 3 = 4 by norm_num, Real.rpow_ofNat]
    exact (show Even (4 : ℕ) from ⟨2, by norm_num⟩).pow_abs (X ω)
  rw [hfg, hfp, hgp] at h
  norm_num at h ⊢
  exact h

/-- The same interpolation written without fractional exponents for exact-constant arithmetic. -/
theorem moment_interpolation_cubic_of_bound [IsFiniteMeasure μ] {X : Ω → ℝ}
    (hX : AEMeasurable X μ) {B : ℝ} (hB : ∀ᵐ ω ∂μ, |X ω| ≤ B) :
    (∫ ω, X ω ^ 2 ∂μ) ^ 3 ≤ (∫ ω, |X ω| ∂μ) ^ 2 * (∫ ω, X ω ^ 4 ∂μ) := by
  have h := moment_interpolation_of_bound hX hB
  have h1 : 0 ≤ ∫ ω, |X ω| ∂μ := integral_nonneg (fun _ => abs_nonneg _)
  have h4 : 0 ≤ ∫ ω, X ω ^ 4 ∂μ := integral_nonneg (fun _ => by positivity)
  have h2 : 0 ≤ ∫ ω, X ω ^ 2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have h' := pow_le_pow_left₀ h2 h 3
  have heq : ((∫ ω, |X ω| ∂μ) ^ ((2 : ℝ) / 3) *
      (∫ ω, X ω ^ 4 ∂μ) ^ ((1 : ℝ) / 3)) ^ 3 =
      (∫ ω, |X ω| ∂μ) ^ 2 * (∫ ω, X ω ^ 4 ∂μ) := by
    rw [mul_pow, ← Real.rpow_mul_natCast h1, ← Real.rpow_mul_natCast h4]
    norm_num
  rwa [heq] at h'

end Bounds

section Drift

variable {ι Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- The pathwise Hölder step for the mean-reversion drift (A.5). -/
theorem sum_abs_rpow_le (s : Finset ι) (ε : ι → ℝ) {a : ℝ} (ha : 0 < a) :
    (∑ i ∈ s, |ε i| ^ a) ≤ (s.card : ℝ) ^ (1 / (a + 1)) *
      (∑ i ∈ s, |ε i| ^ (a + 1)) ^ (a / (a + 1)) := by
  have ha1 : 0 < a + 1 := by linarith
  have hpq : Real.HolderConjugate ((a + 1) / a) (a + 1) := by
    rw [Real.holderConjugate_iff]
    constructor
    · exact (lt_div_iff₀ ha).2 (by linarith)
    · field_simp
  have h := Real.inner_le_Lp_mul_Lq_of_nonneg s
    (f := fun i => |ε i| ^ a) (g := fun _ => (1 : ℝ)) hpq
    (fun i _ => Real.rpow_nonneg (abs_nonneg _) _) (fun _ _ => zero_le_one)
  have he : 1 / ((a + 1) / a) = a / (a + 1) := by field_simp
  have hf : (∑ i ∈ s, (|ε i| ^ a) ^ ((a + 1) / a)) =
      ∑ i ∈ s, |ε i| ^ (a + 1) := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  simpa only [one_rpow, mul_one, hf, he, Finset.sum_const, nsmul_eq_mul,
    mul_one, Nat.cast_id, mul_comm] using h

/-- Jensen's concave-power step, without finite-support assumptions. -/
theorem integral_rpow_le_of_concave [IsProbabilityMeasure μ] {G : Ω → ℝ} {r : ℝ}
    (hr0 : 0 ≤ r) (hr1 : r ≤ 1) (hG0 : 0 ≤ᵐ[μ] G)
    (hG : Integrable G μ) (hGr : Integrable (fun ω => G ω ^ r) μ) :
    (∫ ω, G ω ^ r ∂μ) ≤ (∫ ω, G ω ∂μ) ^ r := by
  exact (Real.concaveOn_rpow hr0 hr1).le_map_integral
    (Real.continuous_rpow_const hr0).continuousOn isClosed_Ici hG0 hG hGr

/-- Integral drift bound in Appendix A, with its actual pointwise energy hypotheses. -/
theorem drift_integral_le [IsProbabilityMeasure μ] (s : Finset ι)
    (ε d : ι → Ω → ℝ) (G : Ω → ℝ) {a : ℝ} (ha : 0 < a)
    (hd : ∀ᵐ ω ∂μ, ∀ i ∈ s, |d i ω| ≤ |ε i ω| ^ a)
    (he : ∀ᵐ ω ∂μ, (∑ i ∈ s, |ε i ω| ^ (a + 1)) ≤ G ω)
    (hG0 : 0 ≤ᵐ[μ] G)
    (hD : Integrable (fun ω => |∑ i ∈ s, d i ω|) μ)
    (hG : Integrable G μ)
    (hGr : Integrable (fun ω => G ω ^ (a / (a + 1))) μ) :
    (∫ ω, |∑ i ∈ s, d i ω| ∂μ) ≤
      (s.card : ℝ) ^ (1 / (a + 1)) * (∫ ω, G ω ∂μ) ^ (a / (a + 1)) := by
  have ha1 : 0 < a + 1 := by linarith
  have hr0 : 0 ≤ a / (a + 1) := (div_pos ha ha1).le
  have hr1 : a / (a + 1) ≤ 1 := (div_le_one ha1).2 (by linarith)
  have hpath : ∀ᵐ ω ∂μ, |∑ i ∈ s, d i ω| ≤
      (s.card : ℝ) ^ (1 / (a + 1)) * G ω ^ (a / (a + 1)) := by
    filter_upwards [hd, he] with ω hdω heω
    calc
      |∑ i ∈ s, d i ω| ≤ ∑ i ∈ s, |d i ω| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ s, |ε i ω| ^ a := Finset.sum_le_sum hdω
      _ ≤ (s.card : ℝ) ^ (1 / (a + 1)) *
          (∑ i ∈ s, |ε i ω| ^ (a + 1)) ^ (a / (a + 1)) :=
        sum_abs_rpow_le s (fun i => ε i ω) ha
      _ ≤ (s.card : ℝ) ^ (1 / (a + 1)) * G ω ^ (a / (a + 1)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg (Nat.cast_nonneg _) _)
        exact Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => Real.rpow_nonneg (abs_nonneg _) _))
          heω hr0
  calc
    _ ≤ ∫ ω, (s.card : ℝ) ^ (1 / (a + 1)) * G ω ^ (a / (a + 1)) ∂μ :=
      integral_mono_ae hD (hGr.const_mul _) hpath
    _ = (s.card : ℝ) ^ (1 / (a + 1)) * ∫ ω, G ω ^ (a / (a + 1)) ∂μ :=
      integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_rpow_le_of_concave hr0 hr1 hG0 hG hGr)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)

end Drift
end CalibrationDistance
