import Paper14.GraphLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- A uniform finite-partial first moment bound survives all component
weak limits and the subsequent countable sum. -/
theorem weighted_mass_bound_of_weak_limits {E : Type*} [MeasurableSpace E]
    [TopologicalSpace E] [OpensMeasurableSpace E]
    {νn : ℕ → ℕ → FiniteMeasure E} {η : ℕ → FiniteMeasure E}
    (hlim : ∀ j, Tendsto (fun n => νn n j) atTop (𝓝 (η j))) (C : ℝ≥0)
    (hbound : ∀ n J, ∑ j ∈ Finset.range J, (j : ℝ≥0)*(νn n j).mass ≤ C) :
    (∑' j : ℕ, (j : ℝ≥0∞)*(η j : Measure E) univ) ≤ (C : ℝ≥0∞) := by
  have hpart (J : ℕ) : (∑ j ∈ Finset.range J, (j : ℝ≥0)*(η j).mass) ≤ C := by
    apply le_of_tendsto (tendsto_finset_sum (Finset.range J)
      (fun j hj => (hlim j).mass.const_mul (j : ℝ≥0)))
    exact Eventually.of_forall (fun n => hbound n J)
  rw [ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro J
  have hh := ENNReal.coe_le_coe.mpr (hpart J)
  simpa only [ENNReal.coe_finset_sum,ENNReal.coe_mul,ENNReal.coe_natCast,FiniteMeasure.ennreal_mass] using hh

lemma excessGraph_mass {E : Type*} [MeasurableSpace E]
    {T : E → E} (hT : Measurable T) (μ : Measure E) (Y : Set E) (n j : ℕ) :
    ((excessGraphFinite T μ Y n j).mass : ℝ≥0∞) = normalizedRestriction μ Y (excessLevel T Y n j) := by
  rw [FiniteMeasure.ennreal_mass]
  change Measure.map (fun x => (x,T^[n] x))
    ((normalizedRestriction μ Y).restrict (excessLevel T Y n j)) univ = _
  rw [Measure.map_apply (measurable_graph (hT.iterate n)) MeasurableSet.univ]
  simp only [preimage_univ,Measure.restrict_apply_univ]

/-- The actual finite-partial graph first moment is bounded by the Kac
excess mean, giving the input for the limiting weighted mass theorem. -/
theorem excessGraph_weighted_partial_le {E : Type*} [MeasurableSpace E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T φ : E → E}
    (hT : Ergodic T μ) {Y : Set E} (hY : MeasurableSet Y) (hp : 0 < μ Y)
    (hφ : MeasurePreserving φ μ (normalizedRestriction μ Y))
    (hc : ∀ᵐ x ∂μ, inducedMap T Y (φ x) = φ (T x)) (n J : ℕ) :
    ((∑ j ∈ Finset.range J, (j : ℝ≥0)*(excessGraphFinite T μ Y n j).mass : ℝ≥0) : ℝ) ≤
      (n : ℝ)*((μ Y).toReal⁻¹-1) := by
  let ν := normalizedRestriction μ Y
  letI : IsProbabilityMeasure ν := normalizedRestriction_probability hp.ne'
  have hE (j : ℕ) : MeasurableSet (excessLevel T Y n j) :=
    hY.inter ((measurableSet_singleton j).preimage (measurable_excessDn hT.measurable hY n))
  have hm (j : ℕ) : ((excessGraphFinite T μ Y n j).mass : ℝ) = ν.real (excessLevel T Y n j) :=
    by
      have hh := congrArg ENNReal.toReal (excessGraph_mass hT.measurable μ Y n j)
      simpa only [ENNReal.coe_toReal] using hh
  let f : E → ℝ := fun x => ∑ j ∈ Finset.range J,
    (excessLevel T Y n j).indicator (fun _ => (j : ℝ)) x
  have hfi : Integrable f ν := by
    apply integrable_finset_sum
    intro j hj
    exact (integrable_const (j : ℝ)).indicator (hE j)
  have hfle (x : E) : f x ≤ (excessDn T Y n x : ℝ) := by
    by_cases hx : x ∈ Y
    · have heq : f x = if excessDn T Y n x < J then (excessDn T Y n x : ℝ) else 0 := by
        have ht (j : ℕ) : (excessLevel T Y n j).indicator (fun _ => (j : ℝ)) x =
            if j = excessDn T Y n x then (j : ℝ) else 0 := by
          by_cases hj : j = excessDn T Y n x
          · simp [Set.indicator,excessLevel,hx,hj]
          · simp [Set.indicator,excessLevel,hx,Ne.symm hj,hj]
        change (∑ j ∈ Finset.range J, (excessLevel T Y n j).indicator (fun _ => (j : ℝ)) x) = _
        simp_rw [ht]
        simp only [Finset.sum_ite_eq',Finset.mem_range]
      rw [heq]
      split_ifs
      · exact le_rfl
      · exact Nat.cast_nonneg _
    · have hf0 : f x = 0 := by
        apply Finset.sum_eq_zero
        intro j hj
        exact indicator_of_notMem (fun h => hx h.1) _
      rw [hf0]
      exact Nat.cast_nonneg _
  have hr : Integrable (fun x => (firstReturnTime T Y x : ℝ)) ν := by
    apply Integrable.of_integral_ne_zero
    rw [normalized_firstReturn_mean hT hY hp]
    exact inv_ne_zero (ENNReal.toReal_pos hp.ne' (measure_ne_top μ Y)).ne'
  have hTY := induced_preserves_of_conjugacy hT.toMeasurePreserving hY hφ hc
  have hDi := integrable_excess_of_return_integrable hT.measurable hY hTY hr n
  have hsum : ((∑ j ∈ Finset.range J, (j : ℝ≥0)*(excessGraphFinite T μ Y n j).mass : ℝ≥0) : ℝ) =
      ∫ x, f x ∂ν := by
    push_cast
    rw [integral_finset_sum (Finset.range J)]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [hm j,integral_indicator (hE j),integral_const]
      simp only [Measure.real,Measure.restrict_apply_univ,smul_eq_mul,mul_comm]
    · intro j hj
      exact (integrable_const (j : ℝ)).indicator (hE j)
  rw [hsum]
  calc _ ≤ ∫ x, (excessDn T Y n x : ℝ) ∂ν := integral_mono hfi hDi hfle
       _ = _ := conjugate_induced_excess_first_moment hT hY hp hφ hc n

end
end Paper14
