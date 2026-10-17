import Paper14.SetIntegralBounds
import Paper14.MeasurableMapLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction symmDiff
namespace Paper14
noncomputable section

lemma excessGraphMeasure_smul_restrict {E : Type*} [MeasurableSpace E]
    {T : E → E} (hT : Measurable T) (μ : Measure E) {Y : Set E}
    (hY : MeasurableSet Y) (n j : ℕ) :
    excessGraphMeasure T μ Y n j = (μ Y)⁻¹ • graphMeasure (T^[n]) (μ.restrict (excessLevel T Y n j)) := by
  have hE : MeasurableSet (excessLevel T Y n j) :=
    hY.inter ((measurableSet_singleton j).preimage (measurable_excessDn hT hY n))
  have hsub : excessLevel T Y n j ⊆ Y := fun _ hx => hx.1
  rw [excessGraphMeasure,normalizedRestriction,Measure.restrict_smul,Measure.restrict_restrict hE,
    inter_eq_left.mpr hsub,graphMeasure,Measure.map_smul]
  rfl

/-- Equation (8) controls the actual normalized excess graph invariance
error; no invariant limiting measure is assumed here. -/
theorem excessGraph_invariance_error {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [SecondCountableTopology E] [BorelSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : MeasurePreserving T μ μ) {Y : Set E} (hY : MeasurableSet Y)
    (n j : ℕ) (F : (E × E) →ᵇ ℝ) :
    |(∫ z, F (T z.1,T z.2) ∂excessGraphMeasure T μ Y n j) -
      ∫ z, F z ∂excessGraphMeasure T μ Y n j| ≤
      (μ Y).toReal⁻¹ * ‖F‖ * μ.real (excessLevel T Y n j ∆ (T ⁻¹' excessLevel T Y n j)) := by
  have hE : MeasurableSet (excessLevel T Y n j) :=
    hY.inter ((measurableSet_singleton j).preimage (measurable_excessDn hT.measurable hY n))
  rw [excessGraphMeasure_smul_restrict hT.measurable μ hY,integral_smul_measure,integral_smul_measure]
  simp only [ENNReal.toReal_inv,smul_eq_mul,← mul_sub,abs_mul,abs_inv,
    abs_of_nonneg ENNReal.toReal_nonneg]
  have hc : 0 ≤ (μ Y).toReal⁻¹ := inv_nonneg.mpr ENNReal.toReal_nonneg
  calc _ ≤ (μ Y).toReal⁻¹ * (‖F‖ * μ.real (excessLevel T Y n j ∆ (T ⁻¹' excessLevel T Y n j))) :=
          mul_le_mul_of_nonneg_left (graph_restrict_invariance_error hT n hE F) hc
       _ = _ := by ring

/-- Vanishing graph-test errors give genuine invariance of the weak limit.
The measurable map passage is supplied by the dominated marginal theorem. -/
theorem weak_limit_invariant_of_graph_errors {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    (μ : FiniteMeasure E) {T : E → E} (hT : MeasurePreserving T (μ : Measure E) μ)
    {ηn : ℕ → FiniteMeasure (E × E)} {η : FiniteMeasure (E × E)}
    (hlim : Tendsto ηn atTop (𝓝 η)) (C : ℝ≥0)
    (hf : ∀ n, (ηn n : Measure (E × E)).fst ≤ C • (μ : Measure E))
    (hg : ∀ n, (ηn n : Measure (E × E)).snd ≤ C • (μ : Measure E))
    (herr : ∀ F : (E × E) →ᵇ ℝ,
      Tendsto (fun n => (∫ z, F (T z.1,T z.2) ∂(ηn n : Measure (E × E))) -
        ∫ z, F z ∂(ηn n : Measure (E × E))) atTop (𝓝 0)) :
    MeasurePreserving (Prod.map T T) (η : Measure (E × E)) η := by
  have hV : Measurable (Prod.map T T) := hT.measurable.prodMap hT.measurable
  refine ⟨hV,?_⟩
  have heq : η.map (Prod.map T T) = η := by
    apply FiniteMeasure.ext_of_forall_integral_eq
    intro F
    have hleft := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp
      (weak_limit_map_prod μ hlim C hf hg hT hT) F
    have hright := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hlim F
    have hdiff := hleft.sub hright
    have hrewrite (κ : FiniteMeasure (E × E)) :
        (∫ z, F z ∂(κ.map (Prod.map T T) : Measure (E × E))) =
          ∫ z, F (T z.1,T z.2) ∂(κ : Measure (E × E)) := by
      rw [FiniteMeasure.toMeasure_map,integral_map hV.aemeasurable F.continuous.measurable.aestronglyMeasurable]
      rfl
    simp only [hrewrite] at hdiff
    rw [hrewrite]
    exact sub_eq_zero.mp (tendsto_nhds_unique hdiff (herr F))
  exact congrArg FiniteMeasure.toMeasure heq

/-- Every actual weak limit of excess graph components is simultaneously
invariant, with equation (8) derived from the self-induction conjugacy. -/
theorem excessGraph_limit_invariant {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E}
    (hT : MeasurePreserving T μ μ) (Y : ℕ → Set E) (φ : ℕ → E → E)
    (hY : ∀ n, MeasurableSet (Y n)) (hp : ∀ n, 0 < μ (Y n))
    (hφ : ∀ n, MeasurePreserving (φ n) μ (normalizedRestriction μ (Y n)))
    (hc : ∀ n, ∀ᵐ x ∂μ, inducedMap T (Y n) (φ n x) = φ n (T x))
    (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    (C : ℝ≥0) (hC : ∀ n, (μ (Y n))⁻¹ ≤ (C : ℝ≥0∞))
    (a : ℕ → ℕ) (j : ℕ) {η : FiniteMeasure (E × E)}
    (hlim : Tendsto (fun n => excessGraphFinite T μ (Y n) (a n) j) atTop (𝓝 η)) :
    MeasurePreserving (Prod.map T T) (η : Measure (E × E)) η := by
  let μf : FiniteMeasure E := ⟨μ,inferInstance⟩
  have hsmul (n : ℕ) : (μ (Y n))⁻¹ • μ ≤ C • μ := by
    apply Measure.le_iff.mpr
    intro A hA
    simp only [Measure.smul_apply,smul_eq_mul,Measure.coe_nnreal_smul_apply]
    exact mul_le_mul_right' (hC n) (μ A)
  have hmarg (n : ℕ) :
      (excessGraphMeasure T μ (Y n) (a n) j).fst ≤ C • μ ∧
      (excessGraphMeasure T μ (Y n) (a n) j).snd ≤ C • μ := by
    obtain ⟨hf,hg⟩ := excessGraphMeasure_marginals (Y n) hT (a n) j
    exact ⟨hf.trans (hsmul n),hg.trans (hsmul n)⟩
  apply weak_limit_invariant_of_graph_errors μf hT hlim C
    (fun n => (hmarg n).1) (fun n => (hmarg n).2)
  intro F
  have hcomp : Tendsto (fun n => μ.real (Y n)ᶜ) atTop (𝓝 0) := by
    simpa only [measureReal_compl (hY _),measureReal_univ_eq_one,sub_self] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hρ
  have hsd (n : ℕ) : μ.real (excessLevel T (Y n) (a n) j ∆
      (T ⁻¹' excessLevel T (Y n) (a n) j)) ≤ 3*μ.real (Y n)ᶜ := by
    have ht := ENNReal.toReal_mono (show 3*μ (Y n)ᶜ ≠ ⊤ by finiteness)
      (conjugate_excess_almost_invariant hT (hY n) (hp n) (hφ n) (hc n) (a n) j)
    simpa only [ENNReal.toReal_mul,ENNReal.toReal_ofNat,Measure.real] using ht
  have hsdlim : Tendsto (fun n => μ.real (excessLevel T (Y n) (a n) j ∆
      (T ⁻¹' excessLevel T (Y n) (a n) j))) atTop (𝓝 0) :=
    squeeze_zero (fun _ => measureReal_nonneg) hsd (by simpa using hcomp.const_mul 3)
  have hclim : Tendsto (fun n => (μ (Y n)).toReal⁻¹) atTop (𝓝 1) := by
    simpa using hρ.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
  have hnorm := squeeze_zero (fun _ => abs_nonneg _)
    (fun n => excessGraph_invariance_error hT (hY n) (a n) j F)
    (show Tendsto (fun n => (μ (Y n)).toReal⁻¹*‖F‖*
      μ.real (excessLevel T (Y n) (a n) j ∆ (T ⁻¹' excessLevel T (Y n) (a n) j)))
      atTop (𝓝 0) by simpa using (hclim.mul_const ‖F‖).mul hsdlim)
  exact tendsto_zero_iff_norm_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using hnorm)

end
end Paper14
