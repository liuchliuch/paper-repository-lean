import Paper14.SectionGraphLimits
import Paper14.BoundedProductLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

/-- The set mixing conclusion follows from uniqueness of all subsequential
probability graph limits. Indicators are handled using the proved bounded
measurable product extension. -/
theorem strongMixing_of_graph_limits {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : MeasurePreserving T μ μ)
    (hlimit : ∀ (a : ℕ → ℕ), Tendsto a atTop atTop → ∀ ν : FiniteMeasure (E × E),
      Tendsto (fun n => graphFinite (T^[a n]) μ) atTop (𝓝 ν) → (ν : Measure (E × E)) = μ.prod μ) :
    StrongMixing T μ := by
  intro A C hA hC
  apply tendsto_of_subseq_tendsto
  intro a ha
  obtain ⟨ν,s,hs,hν,_⟩ := finiteMeasure_simultaneous_subsequence
    (fun n (_ : Unit) => graphFinite (T^[a n]) μ) 1
    (fun n _ => (graphFinite_mass_one (hT.measurable.iterate (a n))).le)
  have hνeq := hlimit (fun n => a (s n)) (ha.comp hs.tendsto_atTop) (ν ()) (hν ())
  let P : FiniteMeasure (E × E) := ⟨μ.prod μ,inferInstance⟩
  have hνP : ν () = P := FiniteMeasure.toMeasure_injective hνeq
  have hp : Tendsto (fun n => graphFinite (T^[a (s n)]) μ) atTop (𝓝 P) := by
    simpa only [hνP] using hν ()
  let f : E → ℝ := C.indicator (fun _ => 1)
  let g : E → ℝ := A.indicator (fun _ => 1)
  have hf : Measurable f := measurable_const.indicator hC
  have hg : Measurable g := measurable_const.indicator hA
  have hfb : ∀ x, ‖f x‖ ≤ 1 := by intro x; by_cases hx : x ∈ C <;> simp [f,hx]
  have hgb : ∀ x, ‖g x‖ ≤ 1 := by intro x; by_cases hx : x ∈ A <;> simp [g,hx]
  have hfst (n : ℕ) : (graphFinite (T^[a (s n)]) μ : Measure (E × E)).fst ≤ (1 : ℝ≥0) • μ := by
    change (graphMeasure (T^[a (s n)]) μ).fst ≤ _
    rw [graphMeasure_fst (hT.measurable.iterate _),one_smul]
  have hsnd (n : ℕ) : (graphFinite (T^[a (s n)]) μ : Measure (E × E)).snd ≤ (1 : ℝ≥0) • μ := by
    change (graphMeasure (T^[a (s n)]) μ).snd ≤ _
    rw [graphMeasure_snd (hT.measurable.iterate _),(hT.iterate _).map_eq,one_smul]
  have hPf : (P : Measure (E × E)).fst ≤ (1 : ℝ≥0) • μ := by
    change Measure.map Prod.fst (μ.prod μ) ≤ _
    rw [Measure.map_fst_prod,measure_univ,one_smul,one_smul]
  have hPg : (P : Measure (E × E)).snd ≤ (1 : ℝ≥0) • μ := by
    change Measure.map Prod.snd (μ.prod μ) ≤ _
    rw [Measure.map_snd_prod,measure_univ,one_smul,one_smul]
  have hh := weak_limit_bounded_product hp 1 hfst hsnd hPf hPg hf hg (by norm_num) (by norm_num) hfb hgb
  have htest (n : ℕ) : (∫ z, f z.1*g z.2 ∂(graphFinite (T^[a (s n)]) μ : Measure (E × E))) =
      μ.real ((T^[a (s n)]) ⁻¹' A ∩ C) := by
    have hfg : Measurable (fun z : E × E => f z.1*g z.2) :=
      (hf.comp measurable_fst).mul (hg.comp measurable_snd)
    change (∫ z : E × E, f z.1*g z.2 ∂graphMeasure (T^[a (s n)]) μ) = _
    rw [graph_integral (hT.measurable.iterate _) μ hfg]
    have heq : (fun x => f x*g (T^[a (s n)] x)) =
        ((T^[a (s n)]) ⁻¹' A ∩ C).indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hxA : T^[a (s n)] x ∈ A <;> by_cases hxC : x ∈ C <;> simp [f,g,hxA,hxC]
    rw [heq,integral_indicator ((hT.measurable.iterate _) hA |>.inter hC)]
    simp only [setIntegral_const,smul_eq_mul,mul_one]
  have htarget : (∫ z, f z.1*g z.2 ∂(P : Measure (E × E))) = μ.real C*μ.real A := by
    have heq : (fun z : E × E => f z.1*g z.2) = (C ×ˢ A).indicator (fun _ => (1 : ℝ)) := by
      funext z
      by_cases hc : z.1 ∈ C <;> by_cases ha : z.2 ∈ A <;> simp [f,g,hc,ha]
    rw [heq]
    change (∫ z : E × E, (C ×ˢ A).indicator (fun _ => (1 : ℝ)) z ∂μ.prod μ) = _
    rw [integral_indicator (hC.prod hA),setIntegral_const]
    simp only [smul_eq_mul,mul_one]
    change ((μ.prod μ) (C ×ˢ A)).toReal = _
    rw [Measure.prod_prod,ENNReal.toReal_mul]
    rfl
  simp only [htest,htarget] at hh
  refine ⟨s,?_⟩
  have hENN := ENNReal.tendsto_ofReal hh
  have hevent (n : ℕ) : ENNReal.ofReal (μ.real ((T^[a (s n)]) ⁻¹' A ∩ C)) =
      μ ((T^[a (s n)]) ⁻¹' A ∩ C) := ENNReal.ofReal_toReal (measure_ne_top _ _)
  have hconstant : ENNReal.ofReal (μ.real C*μ.real A) = μ A*μ C := by
    change ENNReal.ofReal ((μ C).toReal*(μ A).toReal) = _
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,ENNReal.ofReal_toReal (measure_ne_top _ _),
      ENNReal.ofReal_toReal (measure_ne_top _ _),mul_comm]
  simpa only [hevent,hconstant] using hENN

end
end Paper14
