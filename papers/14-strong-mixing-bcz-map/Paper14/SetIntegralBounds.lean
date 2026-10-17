import Paper14.BoundedProductLimits
import Paper14.GraphMeasures
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction symmDiff
namespace Paper14
noncomputable section

lemma setIntegral_difference_bound {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsFiniteMeasure μ] {A B : Set E}
    (hA : MeasurableSet A) (hB : MeasurableSet B) {f : E → ℝ} (hf : Measurable f)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x, ‖f x‖ ≤ K) :
    |(∫ x in A, f x ∂μ) - ∫ x in B, f x ∂μ| ≤ K*μ.real (A ∆ B) := by
  have hi := integrable_of_measurable_bound (μ := μ) hf K hb
  have hid := (hi.indicator hA).sub (hi.indicator hB)
  rw [← integral_indicator hA,← integral_indicator hB,← integral_sub (hi.indicator hA) (hi.indicator hB),← Real.norm_eq_abs]
  calc _ ≤ ∫ x, ‖A.indicator f x-B.indicator f x‖ ∂μ := norm_integral_le_integral_norm _
       _ ≤ ∫ x, (A ∆ B).indicator (fun _ => K) x ∂μ := by
         apply integral_mono hid.norm ((integrable_const K).indicator (hA.symmDiff hB))
         intro x
         have hbx : |f x| ≤ K := by simpa only [Real.norm_eq_abs] using hb x
         by_cases ha : x ∈ A <;> by_cases hb' : x ∈ B <;>
           simp [ha,hb',mem_symmDiff,norm_neg,hbx,hK]
       _ = K*μ.real (A ∆ B) := by rw [integral_indicator (hA.symmDiff hB),integral_const]; simp [mul_comm,Measure.real]

lemma setIntegral_preimage_of_mp {E : Type*} [MeasurableSpace E]
    {T : E → E} {μ : Measure E} (hT : MeasurePreserving T μ μ)
    {A : Set E} (hA : MeasurableSet A) {f : E → ℝ} (hf : Measurable f) :
    (∫ x in T ⁻¹' A, f (T x) ∂μ) = ∫ x in A, f x ∂μ := by
  calc _ = ∫ x, f x ∂Measure.map T (μ.restrict (T ⁻¹' A)) :=
         (integral_map hT.measurable.aemeasurable hf.aestronglyMeasurable).symm
       _ = _ := by rw [(hT.restrict_preimage hA).map_eq]

/-- The finite-time graph invariance error is bounded by the actual
symmetric-difference probability appearing in equation (8). -/
theorem graph_restrict_invariance_error {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [SecondCountableTopology E] [BorelSpace E] {μ : Measure E} [IsFiniteMeasure μ]
    {T : E → E} (hT : MeasurePreserving T μ μ) (n : ℕ) {A : Set E}
    (hA : MeasurableSet A) (F : (E × E) →ᵇ ℝ) :
    |(∫ z, F (T z.1,T z.2) ∂graphMeasure (T^[n]) (μ.restrict A)) -
      ∫ z, F z ∂graphMeasure (T^[n]) (μ.restrict A)| ≤ ‖F‖*μ.real (A ∆ (T ⁻¹' A)) := by
  let f : E → ℝ := fun x => F (x,T^[n] x)
  let g : E → ℝ := fun x => f (T x)
  have hf : Measurable f := F.continuous.measurable.comp (measurable_id.prodMk (hT.measurable.iterate n))
  have hg : Measurable g := hf.comp hT.measurable
  have hiter (x : E) : T^[n] (T x) = T (T^[n] x) := iterate_succ_apply T n x |>.symm.trans (iterate_succ_apply' T n x)
  have hFV : Measurable (fun z : E × E => F (T z.1,T z.2)) :=
    F.continuous.measurable.comp (hT.measurable.prodMap hT.measurable)
  have heq1 : (∫ z, F (T z.1,T z.2) ∂graphMeasure (T^[n]) (μ.restrict A)) = ∫ x in A, g x ∂μ := by
    rw [graphMeasure,integral_map (measurable_graph (hT.measurable.iterate n)).aemeasurable
      hFV.aestronglyMeasurable]
    simp only [g,f,hiter]
  have heq2 : (∫ z, F z ∂graphMeasure (T^[n]) (μ.restrict A)) = ∫ x in T ⁻¹' A, g x ∂μ := by
    rw [graphMeasure,integral_map (measurable_graph (hT.measurable.iterate n)).aemeasurable F.continuous.measurable.aestronglyMeasurable]
    exact (setIntegral_preimage_of_mp hT hA hf).symm
  rw [heq1,heq2]
  exact setIntegral_difference_bound hA (hT.measurable hA) hg (norm_nonneg F) (fun x => F.norm_coe_le_norm _)

end
end Paper14
