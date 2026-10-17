import Paper14.LimitComponentBounds
import Paper14.SectionGraphLimits

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal BoundedContinuousFunction
namespace Paper14
noncomputable section

/-- The original two infinite decompositions (9), the finite first moment,
and simultaneous invariance, obtained from actual graph/component weak
limits and the self-induction hypotheses. -/
theorem excess_decomposition_from_limits {E : Type*} [MeasurableSpace E]
    [MetricSpace E] [CompactSpace E] [BorelSpace E] [Nonempty E]
    {μ : Measure E} [IsProbabilityMeasure μ] {T : E → E} (hT : Ergodic T μ)
    (Y : ℕ → Set E) (φ : ℕ → E → E)
    (hY : ∀ n, MeasurableSet (Y n)) (hp : ∀ n, 0 < μ (Y n))
    (hφ : ∀ n, MeasurePreserving (φ n) μ (normalizedRestriction μ (Y n)))
    (hc : ∀ n, ∀ᵐ x ∂μ, inducedMap T (Y n) (φ n x) = φ n (T x))
    (hρ : Tendsto (fun n => μ.real (Y n)) atTop (𝓝 1))
    (hnear : TendstoInMeasure μ φ atTop id)
    (a : ℕ → ℕ) (B C : ℝ≥0)
    (hB : ∀ n, (μ (Y n))⁻¹ ≤ (B : ℝ≥0∞))
    (hC : ∀ n, (a n : ℝ)*((μ (Y n)).toReal⁻¹-1) ≤ C)
    {ν : FiniteMeasure (E × E)} {η : ℕ → FiniteMeasure (E × E)}
    (hgraph : Tendsto (fun n => graphFinite (T^[a n]) μ) atTop (𝓝 ν))
    (hη : ∀ j, Tendsto (fun n => excessGraphFinite T μ (Y n) (a n) j) atTop (𝓝 (η j))) :
    Measure.sum (fun j => (η j : Measure (E × E))) = ν ∧
    Measure.sum (fun j => Measure.map ((secondShift T)^[j]) (η j : Measure (E × E))) = ν ∧
    (∑' j : ℕ, (j : ℝ≥0∞)*(η j : Measure (E × E)) univ) ≤ (C : ℝ≥0∞) ∧
    (∀ j, MeasurePreserving (Prod.map T T) (η j : Measure (E × E)) (η j : Measure (E × E))) ∧
    (∀ j, (η j : Measure (E × E)).fst ≤ μ ∧ (η j : Measure (E × E)).snd ≤ μ) := by
  let μf : FiniteMeasure E := ⟨μ,inferInstance⟩
  let κ : ℕ → ℕ → FiniteMeasure (E × E) := fun n j => excessGraphFinite T μ (Y n) (a n) j
  let M1 : ℕ → FiniteMeasure (E × E) := fun n => sectionGraphFinite T μ (Y n) (a n)
  have hM1 := sectionGraph_tendsto hT.measurable a Y hY hp hρ hgraph
  have hmass1 (n : ℕ) : (M1 n).mass = 1 := sectionGraph_mass_one hT.measurable (hp n) (a n)
  have hfirst : Measure.sum (fun j => (η j : Measure (E × E))) = ν :=
    measure_sum_eq_of_weak_limits_and_tail κ η M1 ν hη hM1 1 C
      (fun n => (hmass1 n).le)
      (fun n J => excessGraph_partial_le hT.measurable μ (hY n) (a n) J)
      (fun n J => excessGraph_head_tail_bound hT (hY n) (hp n) (hφ n) (hc n) (a n) J C (hC n))
  let W := secondShift T
  have hW : Measurable W := measurable_fst.prodMk (hT.measurable.comp measurable_snd)
  let ξ : ℕ → ℕ → FiniteMeasure (E × E) := fun n j => (κ n j).map (W^[j])
  let ζ : ℕ → FiniteMeasure (E × E) := fun j => (η j).map (W^[j])
  let M2 : ℕ → FiniteMeasure (E × E) := fun n =>
    (graphFinite (T^[a n]) μ).map (Prod.map (φ n) (φ n))
  have hM2 := near_identity_graph_tendsto hT.toMeasurePreserving a φ (fun n => (hφ n).measurable) hnear hgraph
  have hmass2 (n : ℕ) : (M2 n).mass = 1 := by
    rw [show M2 n = (graphFinite (T^[a n]) μ).map (Prod.map (φ n) (φ n)) from rfl,
      finiteMeasure_mass_map _ ((hφ n).measurable.prodMap (hφ n).measurable),graphFinite_mass_one (hT.measurable.iterate (a n))]
  have htotal (n : ℕ) : Measure.sum (fun j => (ξ n j : Measure (E × E))) = M2 n := by
    change Measure.sum (fun j => Measure.map ((secondShift T)^[j])
      (excessGraphMeasure T μ (Y n) (a n) j)) =
        Measure.map (Prod.map (φ n) (φ n)) (graphMeasure (T^[a n]) μ)
    rw [sum_shift_excessGraphMeasure hT.toMeasurePreserving (hY n)
      (induced_preserves_of_conjugacy hT.toMeasurePreserving (hY n) (hφ n) (hc n))]
    exact graphMeasure_conjugate hT.toMeasurePreserving (hY n) (hφ n) (hc n) (a n)
  have hξ (j : ℕ) : Tendsto (fun n => ξ n j) atTop (𝓝 (ζ j)) := by
    have hId : MeasurePreserving id μ μ := ⟨measurable_id,Measure.map_id⟩
    have hj : (secondShift T)^[j] = Prod.map id (T^[j]) := by
      funext p
      exact secondShift_iterate T j p.1 p.2
    have hh := weak_limit_map_prod μf (hη j) B
      (fun n => (excessGraph_marginals_le hT.toMeasurePreserving (Y n) (a n) j B (hB n)).1)
      (fun n => (excessGraph_marginals_le hT.toMeasurePreserving (Y n) (a n) j B (hB n)).2)
      hId (hT.toMeasurePreserving.iterate j)
    simpa only [ξ,ζ,κ,W,hj] using hh
  have hhead (n J : ℕ) : (∑ j ∈ Finset.range J, ξ n j).mass = (∑ j ∈ Finset.range J, κ n j).mass := by
    rw [finiteMeasure_mass_sum,finiteMeasure_mass_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact finiteMeasure_mass_map _ (hW.iterate j)
  have hfinite (n J : ℕ) : ((∑ j ∈ Finset.range J, ξ n j : FiniteMeasure (E × E)) : Measure (E × E)) ≤ M2 n := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [finiteMeasure_coe_sum,Measure.finset_sum_apply,← htotal n,Measure.sum_apply _ hA]
    exact ENNReal.sum_le_tsum _
  have htail (n J : ℕ) : (M2 n).mass ≤ (∑ j ∈ Finset.range (J+1), ξ n j).mass + C/((J+1 : ℕ) : ℝ≥0) := by
    rw [hmass2,hhead]
    have hh := excessGraph_head_tail_bound hT (hY n) (hp n) (hφ n) (hc n) (a n) J C (hC n)
    rw [sectionGraph_mass_one hT.measurable (hp n) (a n)] at hh
    exact hh
  have hsecond : Measure.sum (fun j => (ζ j : Measure (E × E))) = ν :=
    measure_sum_eq_of_weak_limits_and_tail ξ ζ M2 ν hξ hM2 1 C
      (fun n => (hmass2 n).le) hfinite htail
  have hmoment : (∑' j : ℕ, (j : ℝ≥0∞)*(η j : Measure (E × E)) univ) ≤ (C : ℝ≥0∞) := by
    apply weighted_mass_bound_of_weak_limits hη C
    intro n J
    apply NNReal.coe_le_coe.mp
    exact (excessGraph_weighted_partial_le hT (hY n) (hp n) (hφ n) (hc n) (a n) J).trans (hC n)
  refine ⟨hfirst,hsecond,hmoment,?_,?_⟩
  · intro j
    exact excessGraph_limit_invariant hT.toMeasurePreserving Y φ hY hp hφ hc hρ B hB a j (hη j)
  · intro j
    exact excessGraph_limit_marginals hT.toMeasurePreserving Y hp hρ B hB a j (hη j)

end
end Paper14
