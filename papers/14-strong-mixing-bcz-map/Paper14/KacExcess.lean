import Paper14.Kac
import Paper14.ExcessFirstMoment
import Mathlib.Probability.ConditionalProbability
open MeasureTheory Measure Filter Set Function
open scoped ENNReal symmDiff
namespace Paper14
noncomputable section

lemma normalizedRestriction_probability {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {Y : Set α} (hY : μ Y ≠ 0) :
    IsProbabilityMeasure (normalizedRestriction μ Y) :=
  ProbabilityTheory.cond_isProbabilityMeasure hY

lemma induced_preserves_of_conjugacy {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α}
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) :
    MeasurePreserving (inducedMap T Y) (normalizedRestriction μ Y)
      (normalizedRestriction μ Y) := by
  have hm := measurable_inducedMap hT.measurable hY
  refine ⟨hm, ?_⟩
  rw [← hφ.map_eq, Measure.map_map hm hφ.measurable]
  have heq : (inducedMap T Y ∘ φ) =ᵐ[μ] (φ ∘ T) := hc
  rw [Measure.map_congr heq, ← Measure.map_map hφ.measurable hT.measurable, hT.map_eq]

lemma normalized_firstReturn_mean {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y) :
    (∫ y, (firstReturnTime T Y y : ℝ) ∂normalizedRestriction μ Y) =
      (μ Y).toReal⁻¹ := by
  rw [normalizedRestriction, integral_smul_measure, ENNReal.toReal_inv,
    kac_integral hT hY hpos, smul_eq_mul, mul_one]

/-- The actual excess first moment (6), now deriving the return mean from
Kac's theorem rather than assuming it. -/
theorem induced_excess_first_moment {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hTY : MeasurePreserving (inducedMap T Y) (normalizedRestriction μ Y)
      (normalizedRestriction μ Y)) (n : ℕ) :
    (∫ y, (excessDn T Y n y : ℝ) ∂normalizedRestriction μ Y) =
      n * ((μ Y).toReal⁻¹ - 1) := by
  haveI := normalizedRestriction_probability hpos.ne'
  have hmean := normalized_firstReturn_mean hT hY hpos
  have hρ : 0 < (μ Y).toReal := ENNReal.toReal_pos hpos.ne' (measure_ne_top μ Y)
  have hint : Integrable (fun y => (firstReturnTime T Y y : ℝ)) (normalizedRestriction μ Y) := by
    apply Integrable.of_integral_ne_zero
    rw [hmean]
    exact inv_ne_zero hρ.ne'
  have hraw : ∀ᵐ y ∂μ.restrict Y, 0 < firstReturnTime T Y y := by
    rw [ae_restrict_iff' hY]
    filter_upwards [ae_return_exists hT.toMeasurePreserving hY] with y hy hmem
    exact (firstReturn_spec (hy hmem)).1
  have hbase : ∀ᵐ y ∂normalizedRestriction μ Y, 0 < firstReturnTime T Y y :=
    Measure.ae_smul_measure hraw ((μ Y)⁻¹)
  have hrec : ∀ᵐ y ∂normalizedRestriction μ Y, ∀ i : ℕ,
      0 < firstReturnTime T Y ((inducedMap T Y)^[i] y) :=
    ae_all_iff.mpr (fun i : ℕ => (hTY.iterate i).quasiMeasurePreserving.ae
      (p := fun y => 0 < firstReturnTime T Y y) hbase)
  exact integral_excess_of_return_mean hTY hint hrec hmean n

/-- The hypotheses in Theorem 4(i) give the preservation needed in (6). -/
theorem conjugate_induced_excess_first_moment {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n : ℕ) :
    (∫ y, (excessDn T Y n y : ℝ) ∂normalizedRestriction μ Y) =
      n * ((μ Y).toReal⁻¹ - 1) :=
  induced_excess_first_moment hT hY hpos
    (induced_preserves_of_conjugacy hT.toMeasurePreserving hY hφ hc) n

lemma induced_restriction_of_conjugacy {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) :
    MeasurePreserving (inducedMap T Y) (μ.restrict Y) (μ.restrict Y) := by
  have h := (induced_preserves_of_conjugacy hT hY hφ hc).smul_measure (μ Y)
  simpa only [normalizedRestriction, smul_smul,
    ENNReal.mul_inv_cancel hpos.ne' (measure_ne_top μ Y), one_smul] using h

/-- The estimate (8) directly from a measure-preserving self-induction. -/
theorem conjugate_excess_almost_invariant {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α} [IsFiniteMeasure μ]
    (hT : MeasurePreserving T μ μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n j : ℕ) :
    μ (excessLevel T Y n j ∆ (T ⁻¹' excessLevel T Y n j)) ≤ 3 * μ Yᶜ :=
  excessLevel_almost_invariant hT hY (induced_restriction_of_conjugacy hT hY hpos hφ hc) n j

lemma integrable_excess_of_return_integrable {α : Type*} [MeasurableSpace α]
    {T : α → α} {Y : Set α} {ν : Measure α}
    (hT : Measurable T) (hY : MeasurableSet Y)
    (hTY : MeasurePreserving (inducedMap T Y) ν ν)
    (hr : Integrable (fun y => (firstReturnTime T Y y : ℝ)) ν) (n : ℕ) :
    Integrable (fun y => (excessDn T Y n y : ℝ)) ν := by
  have hR : Measurable (Rn T Y n) := by
    unfold Rn
    apply Finset.measurable_sum
    intro i hi
    exact (measurable_firstReturn hT hY).comp (hTY.iterate i).measurable
  have hE : Measurable (fun y => (excessDn T Y n y : ℝ)) :=
    measurable_from_nat.comp (hR.sub_const n)
  have hRint : Integrable (fun y => (Rn T Y n y : ℝ)) ν := by
    simpa only [Rn, Nat.cast_sum] using
      integrable_finset_sum (Finset.range n)
        (fun i _ => (hTY.iterate i).integrable_comp_of_integrable hr)
  apply hRint.mono' hE.aestronglyMeasurable
  filter_upwards [] with y
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Nat.sub_le (Rn T Y n y) n)

/-- The actual tail bound (7) with the Kac excess mean in its numerator. -/
theorem conjugate_excess_tail {α : Type*} [MeasurableSpace α]
    {T φ : α → α} {Y : Set α} {μ : Measure α} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (hY : MeasurableSet Y) (hpos : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n J : ℕ) :
    normalizedRestriction μ Y {y | J < excessDn T Y n y} ≤
      ENNReal.ofReal ((n : ℝ) * ((μ Y).toReal⁻¹ - 1) / (J + 1)) := by
  haveI := normalizedRestriction_probability hpos.ne'
  have hTY := induced_preserves_of_conjugacy hT.toMeasurePreserving hY hφ hc
  have hmean := normalized_firstReturn_mean hT hY hpos
  have hr : Integrable (fun y => (firstReturnTime T Y y : ℝ)) (normalizedRestriction μ Y) := by
    apply Integrable.of_integral_ne_zero
    rw [hmean]
    exact inv_ne_zero (ENNReal.toReal_pos hpos.ne' (measure_ne_top μ Y)).ne'
  exact nat_tail_measure_le (excessDn T Y n) J
    (integrable_excess_of_return_integrable hT.measurable hY hTY hr n)
    (conjugate_induced_excess_first_moment hT hY hpos hφ hc n).le

end
end Paper14
