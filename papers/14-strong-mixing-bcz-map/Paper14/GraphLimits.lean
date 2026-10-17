import Paper14.GraphMeasures
import Paper14.MeasureLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

lemma normalizedRestriction_zeroOrProbability {E : Type*} [MeasurableSpace E]
    (μ : Measure E) (Y : Set E) : IsZeroOrProbabilityMeasure (normalizedRestriction μ Y) := by
  change IsZeroOrProbabilityMeasure (ProbabilityTheory.cond μ Y)
  infer_instance

/-- The genuine excess graph measure, packaged as a finite measure. -/
def excessGraphFinite {E : Type*} [MeasurableSpace E]
    (T : E → E) (μ : Measure E) (Y : Set E) (n j : ℕ) : FiniteMeasure (E × E) := by
  letI := normalizedRestriction_zeroOrProbability μ Y
  exact ⟨excessGraphMeasure T μ Y n j, by unfold excessGraphMeasure graphMeasure; infer_instance⟩

lemma excessGraphFinite_mass_le_one {E : Type*} [MeasurableSpace E]
    {T : E → E} (hT : Measurable T) (μ : Measure E) (Y : Set E) (n j : ℕ) :
    (excessGraphFinite T μ Y n j).mass ≤ 1 := by
  letI := normalizedRestriction_zeroOrProbability μ Y
  apply ENNReal.coe_le_coe.mp
  rw [FiniteMeasure.ennreal_mass,ENNReal.coe_one]
  change graphMeasure (T^[n]) ((normalizedRestriction μ Y).restrict (excessLevel T Y n j)) univ ≤ 1
  rw [graphMeasure,Measure.map_apply (measurable_graph (hT.iterate n)) MeasurableSet.univ]
  simp only [preimage_univ,Measure.restrict_apply_univ]
  exact prob_le_one

/-- The actual simultaneous excess-component extraction of paper Ex22,
valid along any previously chosen sequence of times. -/
theorem excessGraph_simultaneous_subsequence {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {T : E → E} (hT : Measurable T) (μ : Measure E) (Y : ℕ → Set E) (a : ℕ → ℕ) :
    ∃ (η : ℕ → FiniteMeasure (E × E)) (s : ℕ → ℕ), StrictMono s ∧
      (∀ j, Tendsto (fun n => excessGraphFinite T μ (Y (a (s n))) (a (s n)) j)
        atTop (𝓝 (η j))) ∧ (∀ j, (η j).mass ≤ 1) :=
  finiteMeasure_simultaneous_subsequence
    (fun n j => excessGraphFinite T μ (Y (a n)) (a n) j) 1
    (fun n j => excessGraphFinite_mass_le_one hT μ _ _ j)

/-- Both actual limiting component marginals are dominated by the fixed
reference measure, when the finite-time scalar bounds tend to one. -/
theorem weak_limit_marginals_le {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    (μ : FiniteMeasure E) {ηn : ℕ → FiniteMeasure (E × E)} {η : FiniteMeasure (E × E)}
    (hlim : Tendsto ηn atTop (𝓝 η)) {c : ℕ → ℝ≥0}
    (hc : Tendsto c atTop (𝓝 1)) (B : ℝ≥0) (hcB : ∀ n, c n ≤ B)
    (hfst : ∀ n, (ηn n : Measure (E × E)).fst ≤ c n • (μ : Measure E))
    (hsnd : ∀ n, (ηn n : Measure (E × E)).snd ≤ c n • (μ : Measure E)) :
    (η : Measure (E × E)).fst ≤ μ ∧ (η : Measure (E × E)).snd ≤ μ := by
  have hμ : Tendsto (fun n => c n • μ) atTop (𝓝 μ) := by
    simpa using finiteMeasure_tendsto_smul hc (tendsto_const_nhds : Tendsto (fun _ : ℕ => μ) atTop (𝓝 μ))
  have hbound : ∀ n, (c n • μ).mass ≤ B * μ.mass := by
    intro n
    change (c n • μ) univ ≤ B * μ.mass
    rw [FiniteMeasure.smul_apply,smul_eq_mul]
    exact mul_le_mul_of_nonneg_right (hcB n) (zero_le _)
  constructor
  · exact finiteMeasure_le_of_tendsto hμ
      (FiniteMeasure.tendsto_map_of_tendsto_of_continuous ηn η hlim continuous_fst)
      (B * μ.mass) hbound hfst
  · exact finiteMeasure_le_of_tendsto hμ
      (FiniteMeasure.tendsto_map_of_tendsto_of_continuous ηn η hlim continuous_snd)
      (B * μ.mass) hbound hsnd

end
end Paper14
