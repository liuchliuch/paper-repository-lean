import Paper14.InvariantComponents
import Paper14.GraphMeasures

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

lemma secondShift_iterate_fun {E : Type*} (T : E → E) (k : ℕ) :
    (secondShift T)^[k] = fun p : E × E => (p.1,T^[k] p.2) := by
  funext p
  exact secondShift_iterate T k p.1 p.2

/-- The intermediate measure has the weighted scalar marginals asserted
in (10), derived from the component marginals. -/
theorem intermediateMeasure_marginals {E : Type*} [MeasurableSpace E]
    {T : E → E} {μ : Measure E} (hT : MeasurePreserving T μ μ)
    (ν : ℕ → Measure (E × E))
    (hf : ∀ j, (ν j).fst = ν j univ • μ)
    (hg : ∀ j, (ν j).snd = ν j univ • μ) :
    (intermediateMeasure (secondShift T) ν).fst =
      (∑' j : ℕ, (j : ℝ≥0∞)*ν j univ) • μ ∧
    (intermediateMeasure (secondShift T) ν).snd =
      (∑' j : ℕ, (j : ℝ≥0∞)*ν j univ) • μ := by
  have hpair (k : ℕ) : Measurable (fun p : E × E => (p.1,T^[k] p.2)) :=
    measurable_fst.prodMk ((hT.measurable.iterate k).comp measurable_snd)
  have hfst (j k : ℕ) : (Measure.map ((secondShift T)^[k]) (ν j)).fst = ν j univ • μ := by
    rw [Measure.fst,secondShift_iterate_fun,Measure.map_map measurable_fst
      (hpair k)]
    exact hf j
  have hsnd (j k : ℕ) : (Measure.map ((secondShift T)^[k]) (ν j)).snd = ν j univ • μ := by
    rw [Measure.snd,secondShift_iterate_fun,Measure.map_map measurable_snd
      (hpair k)]
    change Measure.map (T^[k] ∘ Prod.snd) (ν j) = _
    rw [← Measure.map_map (hT.measurable.iterate k) measurable_snd]
    change Measure.map (T^[k]) ((ν j).snd) = _
    rw [hg j,Measure.map_smul,(hT.iterate k).map_eq]
  constructor
  · ext A hA
    rw [Measure.fst_apply hA]
    simp only [intermediateMeasure,Measure.sum_apply _ (measurable_fst hA),Measure.finset_sum_apply]
    have ht (j k : ℕ) : Measure.map ((secondShift T)^[k]) (ν j) (Prod.fst ⁻¹' A) = ν j univ * μ A := by
      rw [← Measure.fst_apply (ρ := Measure.map ((secondShift T)^[k]) (ν j)) hA,hfst,
        Measure.smul_apply,smul_eq_mul]
    simp_rw [ht]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Measure.smul_apply,smul_eq_mul]
    simp only [← mul_assoc,ENNReal.tsum_mul_right]
  · ext A hA
    rw [Measure.snd_apply hA]
    simp only [intermediateMeasure,Measure.sum_apply _ (measurable_snd hA),Measure.finset_sum_apply]
    have ht (j k : ℕ) : Measure.map ((secondShift T)^[k]) (ν j) (Prod.snd ⁻¹' A) = ν j univ * μ A := by
      rw [← Measure.snd_apply (ρ := Measure.map ((secondShift T)^[k]) (ν j)) hA,hsnd,
        Measure.smul_apply,smul_eq_mul]
    simp_rw [ht]
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul,Measure.smul_apply,smul_eq_mul]
    simp only [← mul_assoc,ENNReal.tsum_mul_right]

/-- Simultaneous invariance and domination make both component marginal
densities constant, as in paper S3.p6. -/
theorem invariant_component_marginals {E : Type*} [MeasurableSpace E]
    {T : E → E} {μ : Measure E} [IsProbabilityMeasure μ]
    (hT : Ergodic T μ) (ν : Measure (E × E)) [IsFiniteMeasure ν]
    (hV : MeasurePreserving (Prod.map T T) ν ν)
    (hf : ν.fst ≤ μ) (hg : ν.snd ≤ μ) :
    ν.fst = ν univ • μ ∧ ν.snd = ν univ • μ := by
  have hfst : MeasurePreserving T ν.fst ν.fst := by
    refine ⟨hT.measurable,?_⟩
    rw [Measure.fst,Measure.map_map hT.measurable measurable_fst]
    have heq : T ∘ Prod.fst = Prod.fst ∘ Prod.map T T := rfl
    rw [heq,← Measure.map_map measurable_fst hV.measurable,hV.map_eq]
  have hsnd : MeasurePreserving T ν.snd ν.snd := by
    refine ⟨hT.measurable,?_⟩
    rw [Measure.snd,Measure.map_map hT.measurable measurable_snd]
    have heq : T ∘ Prod.snd = Prod.snd ∘ Prod.map T T := rfl
    rw [heq,← Measure.map_map measurable_snd hV.measurable,hV.map_eq]
  constructor
  · simpa only [Measure.fst_univ] using invariant_ac_eq_mass_smul hT hfst (Measure.absolutelyContinuous_of_le hf)
  · simpa only [Measure.snd_univ] using invariant_ac_eq_mass_smul hT hsnd (Measure.absolutelyContinuous_of_le hg)

/-- The full measure-algebra step (9)--(11), deriving the intermediate
marginals instead of requiring them as additional inputs. -/
theorem positive_components_of_invariant_decomposition {E : Type*} [MeasurableSpace E]
    {T : E → E} {μ : Measure E} [IsProbabilityMeasure μ]
    (hweak : WeakMixing T μ) (ν : ℕ → Measure (E × E))
    [IsFiniteMeasure (Measure.sum ν)]
    (hdecomp : Measure.sum ν = Measure.sum (fun j => Measure.map ((secondShift T)^[j]) (ν j)))
    (hmoment : (∑' j : ℕ, (j : ℝ≥0∞)*ν j univ) < ⊤)
    (hV : ∀ j, MeasurePreserving (Prod.map T T) (ν j) (ν j))
    (hf : ∀ j, (ν j).fst ≤ μ) (hg : ∀ j, (ν j).snd ≤ μ) :
    ∀ j : ℕ, 0 < j → ν j = ν j univ • μ.prod μ := by
  have hT : Ergodic T μ := ⟨hweak.1,
    (measurePreserving_fst (μ := μ) (ν := μ)).preErgodic_of_preErgodic_conjugate
      hweak.2.toPreErgodic (fun p => rfl)⟩
  have hfin (j : ℕ) : IsFiniteMeasure (ν j) := isFiniteMeasure_of_le _ (Measure.le_sum ν j)
  have hmarg (j : ℕ) : (ν j).fst = ν j univ • μ ∧ (ν j).snd = ν j univ • μ := by
    letI := hfin j
    exact invariant_component_marginals hT (ν j) (hV j) (hf j) (hg j)
  obtain ⟨hif,his⟩ := intermediateMeasure_marginals hweak.1 ν (fun j => (hmarg j).1) (fun j => (hmarg j).2)
  exact positive_components_of_decomposition hweak ν hdecomp hmoment hif his hV

end
end Paper14
