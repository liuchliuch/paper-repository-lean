import Paper14.GraphTails
import Paper14.ConditioningLimits
import Paper14.NearIdentityGraphs

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

def graphFinite {E : Type*} [MeasurableSpace E]
    (S : E → E) (μ : Measure E) [IsFiniteMeasure μ] : FiniteMeasure (E × E) :=
  ⟨graphMeasure S μ,by unfold graphMeasure; infer_instance⟩

lemma graphFinite_mass_one {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {S : E → E} (hS : Measurable S) :
    (graphFinite S μ).mass = 1 := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass,ENNReal.coe_one]
  change graphMeasure S μ univ = 1
  rw [graphMeasure,Measure.map_apply (measurable_graph hS) MeasurableSet.univ]
  simp only [preimage_univ,measure_univ]

lemma graph_integral {E : Type*} [MeasurableSpace E] {S : E → E}
    (hS : Measurable S) (μ : Measure E) {f : E × E → ℝ} (hf : Measurable f) :
    (∫ z, f z ∂graphMeasure S μ) = ∫ x, f (x,S x) ∂μ := by
  rw [graphMeasure,integral_map (measurable_graph hS).aemeasurable hf.aestronglyMeasurable]

/-- The first total in Ex25 has the same weak limit as the original
probability graph when section masses tend to one. -/
theorem sectionGraph_tendsto {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : Measurable T) (a : ℕ → ℕ) (Y : ℕ → Set E)
    (hY : ∀ n, MeasurableSet (Y n)) (hp : ∀ n, 0 < μ (Y n))
    (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    {ν : FiniteMeasure (E × E)}
    (hlim : Tendsto (fun n => graphFinite (T^[a n]) μ) atTop (𝓝 ν)) :
    Tendsto (fun n => sectionGraphFinite T μ (Y n) (a n)) atTop (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro F
  let f : ℕ → E → ℝ := fun n x => F (x,T^[a n] x)
  have hf : ∀ n, Measurable (f n) := fun n =>
    F.continuous.measurable.comp (measurable_graph (hT.iterate (a n)))
  have he := normalizedRestriction_integral_error_tendsto Y hY hp hρ f hf (norm_nonneg F)
    (fun n x => F.norm_coe_le_norm (x,T^[a n] x))
  have ho := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F
  have hgraph (n : ℕ) : (∫ z, F z ∂(graphFinite (T^[a n]) μ : Measure (E × E))) = ∫ x, f n x ∂μ :=
    graph_integral (hT.iterate (a n)) μ F.continuous.measurable
  have hsection (n : ℕ) : (∫ z, F z ∂(sectionGraphFinite T μ (Y n) (a n) : Measure (E × E))) =
      ∫ x, f n x ∂normalizedRestriction μ (Y n) :=
    graph_integral (hT.iterate (a n)) _ F.continuous.measurable
  simp only [hgraph] at ho
  have hh := he.add ho
  simpa only [sub_add_cancel,zero_add,← hsection] using hh

/-- The second total in Ex26 has the same weak limit: conjugating both
coordinates by maps tending to the identity in measure preserves the
original graph limit, even along arbitrary growing times. -/
theorem near_identity_graph_tendsto {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : MeasurePreserving T μ μ) (a : ℕ → ℕ) (φ : ℕ → E → E)
    (hφ : ∀ n, Measurable (φ n)) (hnear : TendstoInMeasure μ φ atTop id)
    {ν : FiniteMeasure (E × E)}
    (hlim : Tendsto (fun n => graphFinite (T^[a n]) μ) atTop (𝓝 ν)) :
    Tendsto (fun n => (graphFinite (T^[a n]) μ).map (Prod.map (φ n) (φ n))) atTop (𝓝 ν) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro F
  let f : ℕ → E → ℝ := fun n x => F (x,T^[a n] x)
  let g : ℕ → E → ℝ := fun n x => F (φ n x,φ n (T^[a n] x))
  have hf : ∀ n, Measurable (f n) := fun n =>
    F.continuous.measurable.comp (measurable_graph (hT.measurable.iterate (a n)))
  have hg : ∀ n, Measurable (g n) := fun n => F.continuous.measurable.comp
    ((hφ n).prodMk ((hφ n).comp (hT.measurable.iterate (a n))))
  have hi (n : ℕ) : Integrable (f n) μ := integrable_of_measurable_bound (hf n) ‖F‖ (fun x => F.norm_coe_le_norm _)
  have hj (n : ℕ) : Integrable (g n) μ := integrable_of_measurable_bound (hg n) ‖F‖ (fun x => F.norm_coe_le_norm _)
  have he := near_identity_graph_integral_times hT φ hφ hnear F a
  have hsub (n : ℕ) : (∫ x, g n x-f n x ∂μ) = (∫ x, g n x ∂μ)-(∫ x, f n x ∂μ) := integral_sub (hj n) (hi n)
  change Tendsto (fun n => ∫ x, g n x-f n x ∂μ) atTop (𝓝 0) at he
  simp only [hsub] at he
  have ho := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F
  have hgraph (n : ℕ) : (∫ z, F z ∂(graphFinite (T^[a n]) μ : Measure (E × E))) = ∫ x, f n x ∂μ :=
    graph_integral (hT.measurable.iterate (a n)) μ F.continuous.measurable
  have hmap (n : ℕ) :
      (∫ z, F z ∂((graphFinite (T^[a n]) μ).map (Prod.map (φ n) (φ n)) : Measure (E × E))) =
        ∫ x, g n x ∂μ := by
    rw [FiniteMeasure.toMeasure_map]
    change (∫ z, F z ∂Measure.map (Prod.map (φ n) (φ n)) (Measure.map (fun x => (x,T^[a n] x)) μ)) = _
    rw [Measure.map_map ((hφ n).prodMap (hφ n)) (measurable_graph (hT.measurable.iterate (a n))),
      integral_map (((hφ n).prodMap (hφ n)).comp (measurable_graph (hT.measurable.iterate (a n)))).aemeasurable
        F.continuous.measurable.aestronglyMeasurable]
    rfl
  simp only [hgraph] at ho
  have hh := he.add ho
  simpa only [sub_add_cancel,zero_add,← hmap] using hh

end
end Paper14
