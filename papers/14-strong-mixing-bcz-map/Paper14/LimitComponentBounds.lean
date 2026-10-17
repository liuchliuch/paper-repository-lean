import Paper14.MomentLimits
import Paper14.ExcessGraphInvariance

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

lemma finiteMeasure_mass_sum {E ι : Type*} [MeasurableSpace E]
    (s : Finset ι) (ν : ι → FiniteMeasure E) :
    (∑ j ∈ s, ν j).mass = ∑ j ∈ s, (ν j).mass := by
  apply ENNReal.coe_injective
  rw [FiniteMeasure.ennreal_mass,finiteMeasure_coe_sum,Measure.finset_sum_apply,ENNReal.coe_finset_sum]
  simp only [FiniteMeasure.ennreal_mass]

lemma finiteMeasure_mass_map {E F : Type*} [MeasurableSpace E] [MeasurableSpace F]
    (ν : FiniteMeasure E) {f : E → F} (hf : Measurable f) : (ν.map f).mass = ν.mass := by
  change (ν.map f) univ = ν univ
  rw [FiniteMeasure.map_apply ν hf MeasurableSet.univ,preimage_univ]

/-- The actual reciprocal section masses as nonnegative real scalars. -/
def reciprocalSectionMass {E : Type*} [MeasurableSpace E] (μ : Measure E) (Y : Set E) : ℝ≥0 :=
  ⟨(μ Y).toReal⁻¹,inv_nonneg.mpr ENNReal.toReal_nonneg⟩

lemma reciprocalSectionMass_coe {E : Type*} [MeasurableSpace E] {μ : Measure E}
    {Y : Set E} (hp : 0 < μ Y) :
    (reciprocalSectionMass μ Y : ℝ≥0∞) = (μ Y)⁻¹ := by
  rw [← ENNReal.ofReal_coe_nnreal]
  change ENNReal.ofReal ((μ Y).toReal⁻¹) = _
  rw [← ENNReal.toReal_inv,ENNReal.ofReal_toReal (ENNReal.inv_ne_top.mpr hp.ne')]

lemma reciprocalSectionMass_tendsto {E : Type*} [MeasurableSpace E] (μ : Measure E)
    (Y : ℕ → Set E) (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1)) :
    Tendsto (fun n => reciprocalSectionMass μ (Y n)) atTop (𝓝 1) := by
  apply NNReal.tendsto_coe.mp
  simpa only [reciprocalSectionMass,NNReal.coe_mk,NNReal.coe_one,inv_one] using
    hρ.inv₀ (by norm_num : (1 : ℝ) ≠ 0)

/-- The actual component weak limits have both marginals dominated by mu,
using the true varying scalar bound rho_n^-1. -/
theorem excessGraph_limit_marginals {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : MeasurePreserving T μ μ) (Y : ℕ → Set E)
    (hp : ∀ n, 0 < μ (Y n)) (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    (B : ℝ≥0) (hB : ∀ n, (μ (Y n))⁻¹ ≤ (B : ℝ≥0∞))
    (a : ℕ → ℕ) (j : ℕ) {η : FiniteMeasure (E × E)}
    (hlim : Tendsto (fun n => excessGraphFinite T μ (Y n) (a n) j) atTop (𝓝 η)) :
    (η : Measure (E × E)).fst ≤ μ ∧ (η : Measure (E × E)).snd ≤ μ := by
  let μf : FiniteMeasure E := ⟨μ,inferInstance⟩
  have hb (n : ℕ) : reciprocalSectionMass μ (Y n) ≤ B := by
    apply ENNReal.coe_le_coe.mp
    rw [reciprocalSectionMass_coe (hp n)]
    exact hB n
  apply weak_limit_marginals_le μf hlim (reciprocalSectionMass_tendsto μ Y hρ) B hb
  · intro n
    change (excessGraphMeasure T μ (Y n) (a n) j).fst ≤ _
    change _ ≤ (reciprocalSectionMass μ (Y n) : ℝ≥0∞) • μ
    rw [reciprocalSectionMass_coe (hp n)]
    exact (excessGraphMeasure_marginals (Y n) hT (a n) j).1
  · intro n
    change (excessGraphMeasure T μ (Y n) (a n) j).snd ≤ _
    change _ ≤ (reciprocalSectionMass μ (Y n) : ℝ≥0∞) • μ
    rw [reciprocalSectionMass_coe (hp n)]
    exact (excessGraphMeasure_marginals (Y n) hT (a n) j).2

lemma excessGraph_marginals_le {E : Type*} [MeasurableSpace E]
    {μ : Measure E} {T : E → E} (hT : MeasurePreserving T μ μ)
    (Y : Set E) (n j : ℕ) (B : ℝ≥0) (hB : (μ Y)⁻¹ ≤ (B : ℝ≥0∞)) :
    (excessGraphMeasure T μ Y n j).fst ≤ B • μ ∧
    (excessGraphMeasure T μ Y n j).snd ≤ B • μ := by
  have hsmul : (μ Y)⁻¹ • μ ≤ B • μ := by
    apply Measure.le_iff.mpr
    intro A hA
    simp only [Measure.smul_apply,smul_eq_mul]
    exact mul_le_mul_right' hB (μ A)
  obtain ⟨hf,hg⟩ := excessGraphMeasure_marginals Y hT n j
  exact ⟨hf.trans hsmul,hg.trans hsmul⟩

end
end Paper14
