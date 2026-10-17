import CalibrationDistance.Protocol
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory ProbabilityTheory Set
open scoped ProbabilityTheory ENNReal

namespace CalibrationDistance.Protocol

/-- Lebesgue probability on the unit interval. -/
noncomputable def unitUniform : Measure Probability :=
  (volume : Measure ℝ).comap (Subtype.val : Probability → ℝ)

theorem unitUniform_apply {s : Set Probability} (hs : MeasurableSet s) :
    unitUniform s = (volume : Measure ℝ) (Subtype.val '' s) := by
  exact Measure.comap_apply _ Subtype.coe_injective
    (fun _ ht => (MeasurableEmbedding.subtype_coe measurableSet_Icc).measurableSet_image' ht) _ hs

instance unitUniform_probability : IsProbabilityMeasure unitUniform := by
  constructor
  rw [unitUniform_apply MeasurableSet.univ]
  simp only [image_univ, Subtype.range_coe_subtype, setOf_mem_eq, Real.volume_Icc, sub_zero,
    ENNReal.ofReal_one]

/-- Threshold realization with the weak inequality used in the paper. -/
noncomputable def uniformThreshold (q : ℝ) (u : Probability) : Bool :=
  if (u : ℝ) ≤ q then true else false

theorem measurable_uniformThreshold (q : ℝ) : Measurable (uniformThreshold q) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_le measurable_subtype_coe measurable_const

theorem measurable_thresholdPair {H : Type*} [MeasurableSpace H]
    (q : H → ℝ) (hq : Measurable q) :
    Measurable (fun z : H × Probability => uniformThreshold (q z.1) z.2) := by
  apply Measurable.ite _ measurable_const measurable_const
  exact measurableSet_le (measurable_subtype_coe.comp measurable_snd) (hq.comp measurable_fst)

noncomputable def bernoulliMeasure (q : ℝ) : Measure Bool :=
  unitUniform.map (uniformThreshold q)

instance bernoulliMeasure_probability (q : ℝ) : IsProbabilityMeasure (bernoulliMeasure q) := by
  exact Measure.isProbabilityMeasure_map (measurable_uniformThreshold q).aemeasurable

/-- The threshold event has exactly the required success probability, including the endpoints. -/
theorem bernoulliMeasure_true {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    bernoulliMeasure q {true} = ENNReal.ofReal q := by
  rw [bernoulliMeasure, Measure.map_apply (measurable_uniformThreshold q) (measurableSet_singleton true)]
  have hevent : uniformThreshold q ⁻¹' {true} = {u : Probability | (u : ℝ) ≤ q} := by
    ext u
    simp [uniformThreshold]
  rw [hevent, unitUniform_apply (measurableSet_le measurable_subtype_coe measurable_const)]
  have himage : Subtype.val '' {u : Probability | (u : ℝ) ≤ q} = Icc (0:ℝ) q := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact ⟨u.property.1, hu⟩
    · intro hx
      exact ⟨⟨x,hx.1,hx.2.trans hq.2⟩,hx.2,rfl⟩
  rw [himage, Real.volume_Icc, sub_zero]

theorem bernoulliMeasure_false {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) :
    bernoulliMeasure q {false} = 1 - ENNReal.ofReal q := by
  have hc : ({true} : Set Bool)ᶜ = {false} := by
    ext b
    cases b <;> simp
  rw [← hc, measure_compl (measurableSet_singleton true) (measure_ne_top _ _),
    measure_univ, bernoulliMeasure_true hq]

/-- The Bernoulli kernel is constructed by an actual independent uniform draw. -/
noncomputable def bernoulliKernel {H : Type*} [MeasurableSpace H]
    (q : H → ℝ) (hq : Measurable q) : Kernel H Bool :=
  Kernel.deterministic (fun z : H × Probability => uniformThreshold (q z.1) z.2)
    (measurable_thresholdPair q hq) ∘ₖ (Kernel.id ×ₖ Kernel.const H unitUniform)

instance bernoulliKernel_markov {H : Type*} [MeasurableSpace H]
    (q : H → ℝ) (hq : Measurable q) : IsMarkovKernel (bernoulliKernel q hq) := by
  unfold bernoulliKernel
  infer_instance

theorem bernoulliKernel_apply {H : Type*} [MeasurableSpace H]
    (q : H → ℝ) (hq : Measurable q) (h : H) :
    bernoulliKernel q hq h = bernoulliMeasure (q h) := by
  ext s hs
  rw [bernoulliKernel, Kernel.comp_apply' _ _ _ hs]
  rw [Kernel.lintegral_id_prod]
  · simp only [Kernel.const_apply]
    simp_rw [Kernel.deterministic_apply' _ _ hs]
    rw [bernoulliMeasure, Measure.map_apply (measurable_uniformThreshold _) hs]
    rw [← lintegral_indicator_one ((measurable_uniformThreshold (q h)) hs)]
    rfl
  · exact (Kernel.measurable_coe _ hs)

/-- The auxiliary adversary of (5.4), for any measurable history-dependent parameter. -/
noncomputable def bernoulliAdversary
    (q : (n : ℕ) → History n → ℝ) (hq : ∀ n, Measurable (q n)) :
    RandomizedAdversary where
  kernel n := bernoulliKernel (q n) (hq n)
  markov n := inferInstance

end CalibrationDistance.Protocol

namespace CalibrationDistance.Protocol

theorem integral_bernoulliMeasure {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1)
    (f : Bool → ℝ) :
    (∫ y, f y ∂bernoulliMeasure q) = q * f true + (1-q) * f false := by
  rw [integral_fintype f Integrable.of_finite]
  simp only [Fintype.sum_bool, Measure.real, bernoulliMeasure_false hq,
    bernoulliMeasure_true hq, smul_eq_mul]
  rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.mpr hq.2) ENNReal.one_ne_top]
  rw [ENNReal.toReal_one, ENNReal.toReal_ofReal hq.1]

theorem integral_bernoulliKernel {H : Type*} [MeasurableSpace H]
    (q : H → ℝ) (hq : Measurable q) (h : H) (hv : q h ∈ Icc (0:ℝ) 1)
    (f : Bool → ℝ) :
    (∫ y, f y ∂bernoulliKernel q hq h) = q h * f true + (1-q h) * f false := by
  rw [bernoulliKernel_apply]
  exact integral_bernoulliMeasure hv f

end CalibrationDistance.Protocol
