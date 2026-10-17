import Paper14.LimitComponentBounds
import Paper14.InvariantMarginals

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

def excessMarginalFinite {E : Type*} [MeasurableSpace E]
    (T : E → E) (μ : Measure E) (Y : Set E) (n j : ℕ) : FiniteMeasure E :=
  (excessGraphFinite T μ Y n j).map Prod.fst

lemma excessMarginalFinite_coe {E : Type*} [MeasurableSpace E] {T : E → E} (hT : Measurable T)
    (μ : Measure E) (Y : Set E) (n j : ℕ) :
    (excessMarginalFinite T μ Y n j : Measure E)=
      (normalizedRestriction μ Y).restrict (excessLevel T Y n j) := by
  rw [excessMarginalFinite,FiniteMeasure.toMeasure_map]
  exact graphMeasure_fst (hT.iterate n) _

/-- Ergodicity makes every simultaneously extracted excess-level marginal a scalar base measure. -/
theorem excessMarginal_scalar_subsequence {E : Type*} [MeasurableSpace E] [MetricSpace E]
    [CompactSpace E] [BorelSpace E] [Nonempty E] {μ : Measure E} [IsProbabilityMeasure μ]
    {T : E → E} (hT : Ergodic T μ) (Y : ℕ → Set E) (φ : ℕ → E → E)
    (hY : ∀ n,MeasurableSet (Y n)) (hp : ∀ n,0<μ (Y n))
    (hφ : ∀ n,MeasurePreserving (φ n) μ (normalizedRestriction μ (Y n)))
    (hc : ∀ n,∀ᵐ x ∂μ,inducedMap T (Y n) (φ n x)=φ n (T x))
    (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    (B : ℝ≥0) (hB : ∀ n,(μ (Y n))⁻¹≤(B : ℝ≥0∞)) (a : ℕ → ℕ)
    (c : ℕ → ℝ≥0) (hlower : ∀ n j,c j≤(excessGraphFinite T μ (Y n) (a n) j).mass) :
    ∃ (γ : ℕ → ℝ≥0) (s : ℕ → ℕ),StrictMono s ∧ (∀ j,c j≤γ j ∧ γ j≤1) ∧
      ∀ j,Tendsto (fun n => excessMarginalFinite T μ (Y (s n)) (a (s n)) j) atTop
        (𝓝 (⟨(γ j) • μ,inferInstance⟩ : FiniteMeasure E)) := by
  obtain ⟨η,s,hs,hη,hηmass⟩ := finiteMeasure_simultaneous_subsequence
    (fun n j => excessGraphFinite T μ (Y n) (a n) j) 1
    (fun n j => excessGraphFinite_mass_le_one hT.measurable μ _ _ j)
  let γ := fun j => (η j).mass
  refine ⟨γ,s,hs,?_,?_⟩
  · intro j
    exact ⟨ge_of_tendsto (hη j).mass (Eventually.of_forall (fun n => hlower (s n) j)),hηmass j⟩
  · intro j
    have hinv := excessGraph_limit_invariant hT.toMeasurePreserving (fun n => Y (s n)) (fun n => φ (s n))
      (fun n => hY (s n)) (fun n => hp (s n)) (fun n => hφ (s n)) (fun n => hc (s n))
      (hρ.comp hs.tendsto_atTop) B (fun n => hB (s n)) (fun n => a (s n)) j (hη j)
    obtain ⟨hfst,hsnd⟩ := excessGraph_limit_marginals hT.toMeasurePreserving (fun n => Y (s n))
      (fun n => hp (s n)) (hρ.comp hs.tendsto_atTop) B (fun n => hB (s n)) (fun n => a (s n)) j (hη j)
    have hclass := invariant_component_marginals hT (η j : Measure (E × E)) hinv hfst hsnd
    have heq : (η j).map Prod.fst=(⟨(γ j) • μ,inferInstance⟩ : FiniteMeasure E) := by
      apply FiniteMeasure.toMeasure_injective
      rw [FiniteMeasure.toMeasure_map]
      change (η j : Measure (E × E)).fst=((η j).mass : ℝ≥0∞) • μ
      rw [FiniteMeasure.ennreal_mass]
      exact hclass.1
    have ht := FiniteMeasure.tendsto_map_of_tendsto_of_continuous _ _ (hη j) continuous_fst
    rw [heq] at ht
    exact ht

end
end Paper14
