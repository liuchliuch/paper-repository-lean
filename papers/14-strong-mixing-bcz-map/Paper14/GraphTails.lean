import Paper14.GraphLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

def sectionGraphFinite {E : Type*} [MeasurableSpace E]
    (T : E → E) (μ : Measure E) (Y : Set E) (n : ℕ) : FiniteMeasure (E × E) := by
  letI := normalizedRestriction_zeroOrProbability μ Y
  exact ⟨graphMeasure (T^[n]) (normalizedRestriction μ Y),by unfold graphMeasure; infer_instance⟩

lemma excess_head_union {E : Type*} (T : E → E) (Y : Set E) (n J : ℕ) :
    (⋃ j ∈ Finset.range J, excessLevel T Y n j) = Y ∩ {x | excessDn T Y n x < J} := by
  ext x
  simp only [Set.mem_iUnion,Finset.mem_range,mem_excessLevel,mem_inter_iff,mem_setOf_eq]
  exact ⟨fun ⟨j,hj,hx,heq⟩ => ⟨hx,heq ▸ hj⟩,fun ⟨hx,hlt⟩ => ⟨excessDn T Y n x,hlt,hx,rfl⟩⟩

lemma excessGraph_partial_le {E : Type*} [MeasurableSpace E]
    {T : E → E} (hT : Measurable T) (μ : Measure E) {Y : Set E}
    (hY : MeasurableSet Y) (n J : ℕ) :
    ((∑ j ∈ Finset.range J, excessGraphFinite T μ Y n j : FiniteMeasure (E × E)) : Measure (E × E)) ≤
      sectionGraphFinite T μ Y n := by
  apply Measure.le_iff.mpr
  intro A hA
  rw [finiteMeasure_coe_sum,Measure.finset_sum_apply]
  change (∑ j ∈ Finset.range J, excessGraphMeasure T μ Y n j A) ≤
    graphMeasure (T^[n]) (normalizedRestriction μ Y) A
  rw [← sum_excessGraphMeasure μ hT hY n,Measure.sum_apply _ hA]
  exact ENNReal.sum_le_tsum _

/-- The finite graph head mass is the actual truncated excess probability. -/
lemma excessGraph_partial_mass {E : Type*} [MeasurableSpace E]
    {T : E → E} (hT : Measurable T) (μ : Measure E) {Y : Set E}
    (hY : MeasurableSet Y) (n J : ℕ) :
    ((∑ j ∈ Finset.range J, excessGraphFinite T μ Y n j : FiniteMeasure (E × E)).mass : ℝ≥0∞) =
      normalizedRestriction μ Y {x | excessDn T Y n x < J} := by
  have hE (j : ℕ) : MeasurableSet (excessLevel T Y n j) :=
    hY.inter ((measurableSet_singleton j).preimage (measurable_excessDn hT hY n))
  have hD : MeasurableSet {x | excessDn T Y n x < J} :=
    (measurable_excessDn hT hY n) (Set.to_countable {k : ℕ | k < J} |>.measurableSet)
  rw [FiniteMeasure.ennreal_mass,finiteMeasure_coe_sum,Measure.finset_sum_apply]
  have hterm (j : ℕ) : (excessGraphFinite T μ Y n j : Measure (E × E)) univ =
      normalizedRestriction μ Y (excessLevel T Y n j) := by
    change Measure.map (fun x => (x,T^[n] x))
      ((normalizedRestriction μ Y).restrict (excessLevel T Y n j)) univ = _
    rw [Measure.map_apply (measurable_graph (hT.iterate n)) MeasurableSet.univ]
    simp only [preimage_univ,Measure.restrict_apply_univ]
  simp_rw [hterm]
  rw [← measure_biUnion_finset (fun j hj k hk hjk => disjoint_excessLevel hjk) (fun j hj => hE j),excess_head_union]
  calc _ = ((normalizedRestriction μ Y).restrict Y) {x | excessDn T Y n x < J} := by
           rw [Measure.restrict_apply hD,inter_comm]
       _ = _ := by rw [normalizedRestriction_restrict μ hY]

lemma sectionGraph_mass_one {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E} (hT : Measurable T)
    {Y : Set E} (hp : 0 < μ Y) (n : ℕ) :
    (sectionGraphFinite T μ Y n).mass = 1 := by
  letI := normalizedRestriction_probability hp.ne'
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass,ENNReal.coe_one]
  change graphMeasure (T^[n]) (normalizedRestriction μ Y) univ = 1
  rw [graphMeasure,Measure.map_apply (measurable_graph (hT.iterate n)) MeasurableSet.univ]
  simp only [preimage_univ,measure_univ]

/-- The actual uniform tail hypothesis needed by the infinite-decomposition
limit theorem, derived from the source Kac tail bound. -/
theorem excessGraph_head_tail_bound {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T φ : E → E}
    (hT : Ergodic T μ) {Y : Set E} (hY : MeasurableSet Y) (hp : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x))
    (n J : ℕ) (C : ℝ≥0) (hC : (n : ℝ)*((μ Y).toReal⁻¹-1) ≤ C) :
    (sectionGraphFinite T μ Y n).mass ≤
      (∑ j ∈ Finset.range (J+1), excessGraphFinite T μ Y n j : FiniteMeasure (E × E)).mass +
        C/((J+1 : ℕ) : ℝ≥0) := by
  let ν := normalizedRestriction μ Y
  letI : IsProbabilityMeasure ν := normalizedRestriction_probability hp.ne'
  have hD : MeasurableSet {x | excessDn T Y n x < J+1} :=
    (measurable_excessDn hT.measurable hY n) (Set.to_countable {k : ℕ | k < J+1} |>.measurableSet)
  have hcompl : {x | excessDn T Y n x < J+1}ᶜ = {x | J < excessDn T Y n x} := by
    ext x
    simp only [mem_compl_iff,mem_setOf_eq]
    omega
  have hsplit := measureReal_add_measureReal_compl (μ := ν) hD
  rw [hcompl,measureReal_univ_eq_one] at hsplit
  have htail : ν.real {x | J < excessDn T Y n x} ≤ (C : ℝ)/(J+1) := by
    have hbound : ν {x | J < excessDn T Y n x} ≤ ENNReal.ofReal ((C : ℝ)/(J+1)) :=
      (conjugate_excess_tail hT hY hp hφ hc n J).trans
        (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hC (by positivity)))
    have hh := ENNReal.toReal_mono (ENNReal.ofReal_ne_top) hbound
    simpa only [Measure.real,ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ (C : ℝ)/(J+1))] using hh
  have hhead : (((∑ j ∈ Finset.range (J+1), excessGraphFinite T μ Y n j : FiniteMeasure (E × E)).mass : ℝ≥0) : ℝ) =
      ν.real {x | excessDn T Y n x < J+1} := by
    have hh := congrArg ENNReal.toReal (excessGraph_partial_mass hT.measurable μ hY n (J+1))
    exact hh
  rw [sectionGraph_mass_one hT.measurable hp n]
  apply NNReal.coe_le_coe.mp
  push_cast
  rw [hhead]
  linarith

end
end Paper14
