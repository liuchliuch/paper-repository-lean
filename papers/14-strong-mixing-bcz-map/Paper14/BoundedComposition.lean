import Paper14.BoundedProductLimits
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

lemma bounded_continuous_composition_error {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ] (φ : ℕ → E → E)
    (hφ : ∀ n,Measurable (φ n)) (hpoint : ∀ᵐ x ∂μ,Tendsto (fun n => φ n x) atTop (𝓝 x))
    (g : E →ᵇ ℝ) : Tendsto (fun n => ∫ x,‖g (φ n x)-g x‖ ∂μ) atTop (𝓝 0) := by
  have hb (n : ℕ) (x : E) : ‖‖g (φ n x)-g x‖‖≤2*‖g‖ := by
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [g.norm_coe_le_norm (φ n x),g.norm_coe_le_norm x])
  have hp : ∀ᵐ x ∂μ,Tendsto (fun n => ‖g (φ n x)-g x‖) atTop (𝓝 0) := by
    filter_upwards [hpoint] with x hx
    have ht : Tendsto (fun n => g (φ n x)) atTop (𝓝 (g x)) := g.continuous.continuousAt.tendsto.comp hx
    simpa only [sub_self,norm_zero] using (ht.sub (tendsto_const_nhds (x := g x))).norm
  have ht := tendsto_integral_of_dominated_convergence (fun _ : E => 2*‖g‖)
    (fun n => (((g.continuous.measurable.comp (hφ n)).sub g.continuous.measurable).norm).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (hb n)) hp
  simpa only [integral_zero] using ht

/-- Bounded measurable functions are stable under near-identity pullbacks with dominated laws. -/
theorem bounded_composition_L1_error {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    (φ : ℕ → E → E) (hφ : ∀ n,Measurable (φ n))
    (hpoint : ∀ᵐ x ∂μ,Tendsto (fun n => φ n x) atTop (𝓝 x))
    (C : ℝ≥0) (hdom : ∀ n,Measure.map (φ n) μ≤C • μ)
    {f : E → ℝ} (hf : Measurable f) (hb : ∀ x,‖f x‖≤1) :
    Tendsto (fun n => ∫ x,‖f (φ n x)-f x‖ ∂μ) atTop (𝓝 0) := by
  have hfi : Integrable f μ := Integrable.of_bound hf.aestronglyMeasurable 1 (Eventually.of_forall hb)
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  let δ := ε/(8*((C : ℝ)+1))
  have hδ : 0<δ := by dsimp [δ]; positivity
  obtain ⟨g,hg,_⟩ := hfi.exists_boundedContinuous_integral_sub_le hδ
  let e : E → ℝ := fun x => ‖f x-g x‖
  have he : Measurable e := (hf.sub g.continuous.measurable).norm
  have hei : Integrable e μ := (hfi.sub (g.integrable μ)).norm
  have hi (n : ℕ) : Integrable (fun x => e (φ n x)) μ := by
    apply integrable_of_measurable_bound (he.comp (hφ n)) (1+‖g‖)
    intro x
    change ‖‖f (φ n x)-g (φ n x)‖‖≤1+‖g‖
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (add_le_add (hb _) (g.norm_coe_le_norm _))
  have hgi (n : ℕ) : Integrable (fun x => ‖g (φ n x)-g x‖) μ := by
    apply integrable_of_measurable_bound (((g.continuous.measurable.comp (hφ n)).sub g.continuous.measurable).norm) (2*‖g‖)
    intro x
    change ‖‖g (φ n x)-g x‖‖≤2*‖g‖
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [g.norm_coe_le_norm (φ n x),g.norm_coe_le_norm x])
  have hfn (n : ℕ) : Integrable (fun x => ‖f (φ n x)-f x‖) μ := by
    apply integrable_of_measurable_bound (((hf.comp (hφ n)).sub hf).norm) 2
    intro x
    change ‖‖f (φ n x)-f x‖‖≤2
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact (norm_sub_le _ _).trans (by nlinarith [hb (φ n x),hb x])
  have hcomp (n : ℕ) : (∫ x,e (φ n x) ∂μ)≤C*∫ x,e x ∂μ := by
    rw [← integral_map (μ := μ) (hφ n).aemeasurable he.aestronglyMeasurable]
    calc
      _ ≤ ∫ x,e x ∂(C • μ) :=
        integral_mono_measure (hdom n) (Eventually.of_forall (fun x => norm_nonneg _)) (hei.smul_measure ENNReal.coe_ne_top)
      _ = _ := by rw [integral_smul_nnreal_measure]; rfl
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp ((bounded_continuous_composition_error φ hφ hpoint g).eventually
    (Iio_mem_nhds (show (0 : ℝ)<ε/2 by positivity)))
  refine ⟨N,fun n hn => ?_⟩
  have hupper : (∫ x,‖f (φ n x)-f x‖ ∂μ)≤
      (∫ x,e (φ n x) ∂μ)+(∫ x,‖g (φ n x)-g x‖ ∂μ)+(∫ x,e x ∂μ) := by
    rw [← integral_add' (hi n) (hgi n),← integral_add' ((hi n).add (hgi n)) hei]
    apply integral_mono (hfn n) (((hi n).add (hgi n)).add hei)
    intro x
    change ‖f (φ n x)-f x‖≤e (φ n x)+‖g (φ n x)-g x‖+e x
    have h₁ := norm_sub_le_norm_sub_add_norm_sub (f (φ n x)) (g (φ n x)) (f x)
    have h₂ := norm_sub_le_norm_sub_add_norm_sub (g (φ n x)) (g x) (f x)
    dsimp [e]
    rw [norm_sub_rev (g x) (f x)] at h₂
    simp only [Real.norm_eq_abs] at h₁ h₂ ⊢
    linarith
  have hc := hcomp n
  have hsmall := hN n hn
  have hδid : (8*((C : ℝ)+1))*δ=ε := mul_div_cancel₀ _ (by positivity)
  have hcg := mul_le_mul_of_nonneg_left hg C.coe_nonneg
  rw [Real.dist_eq,sub_zero,abs_of_nonneg (integral_nonneg (fun x => norm_nonneg _))]
  change (∫ x,e x ∂μ)≤δ at hg
  linarith

end
end Paper14
