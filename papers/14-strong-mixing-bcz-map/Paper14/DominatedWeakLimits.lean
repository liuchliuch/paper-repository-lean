import Paper14.BoundedProductLimits
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

lemma dominated_integral_approximation {E : Type*} [MeasurableSpace E] [TopologicalSpace E] [BorelSpace E]
    {μ ν : Measure E} [IsFiniteMeasure μ] [IsFiniteMeasure ν] {C : ℝ≥0}
    (hν : ν≤C • μ) {f : E → ℝ} (hf : Measurable f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) (g : E →ᵇ ℝ) :
    |(∫ x,f x ∂ν)-(∫ x,g x ∂ν)|≤C*(∫ x,‖f x-g x‖ ∂μ) := by
  have hfI := integrable_of_measurable_bound (μ := ν) hf B hb
  have heμ : Integrable (fun x => ‖f x-g x‖) μ :=
    ((integrable_of_measurable_bound hf B hb).sub (g.integrable μ)).norm
  have heC : Integrable (fun x => ‖f x-g x‖) (C • μ) := heμ.smul_measure ENNReal.coe_ne_top
  rw [← integral_sub hfI (g.integrable ν),← Real.norm_eq_abs]
  calc
    _ ≤ ∫ x,‖f x-g x‖ ∂ν := norm_integral_le_integral_norm _
    _ ≤ ∫ x,‖f x-g x‖ ∂(C • μ) :=
      integral_mono_measure hν (Eventually.of_forall (fun x => norm_nonneg _)) heC
    _ = _ := by rw [integral_smul_nnreal_measure]; rfl

/-- Uniform measure domination upgrades weak convergence to any fixed bounded measurable test. -/
theorem weak_limit_bounded_measurable {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    {νn : ℕ → FiniteMeasure E} {ν : FiniteMeasure E} (hlim : Tendsto νn atTop (𝓝 ν))
    (C : ℝ≥0) (hdomn : ∀ n,(νn n : Measure E)≤C • μ) (hdom : (ν : Measure E)≤C • μ)
    {f : E → ℝ} (hf : Measurable f) (B : ℝ) (hb : ∀ x,‖f x‖≤B) :
    Tendsto (fun n => ∫ x,f x ∂(νn n : Measure E)) atTop (𝓝 (∫ x,f x ∂(ν : Measure E))) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(8*((C : ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨g,hg,_⟩ := (integrable_of_measurable_bound (μ := μ) hf B hb).exists_boundedContinuous_integral_sub_le hδ
  have herror (η : FiniteMeasure E) (hη : (η : Measure E)≤C • μ) :
      |(∫ x,f x ∂(η : Measure E))-(∫ x,g x ∂(η : Measure E))|≤ε/8 := by
    apply (dominated_integral_approximation hη hf B hb g).trans
    have hh := mul_le_mul_of_nonneg_left hg C.coe_nonneg
    have hid : (8*((C : ℝ)+1))*δ=ε := mul_div_cancel₀ _ (by positivity)
    nlinarith
  obtain ⟨N,hN⟩ := Metric.tendsto_atTop.mp
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim g) (ε/2) (by positivity)
  refine ⟨N,fun n hn => ?_⟩
  have hmid : |(∫ x,g x ∂(νn n : Measure E))-(∫ x,g x ∂(ν : Measure E))|<ε/2 := by
    simpa only [Real.dist_eq] using hN n hn
  have h₁ := herror (νn n) (hdomn n)
  have h₂ := herror ν hdom
  rw [abs_sub_comm] at h₂
  have hh := abs_add_three
    ((∫ x,f x ∂(νn n : Measure E))-(∫ x,g x ∂(νn n : Measure E)))
    ((∫ x,g x ∂(νn n : Measure E))-(∫ x,g x ∂(ν : Measure E)))
    ((∫ x,g x ∂(ν : Measure E))-(∫ x,f x ∂(ν : Measure E)))
  simp only [sub_add_sub_cancel] at hh
  rw [Real.dist_eq]
  linarith

end
end Paper14
