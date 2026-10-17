import Paper14.BCZAdjacentInputs
import Paper14.AdjacentExcessCriterion

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

/-- The original weak-mixing conclusion, with BCZ ergodicity as the only remaining background input. -/
theorem bcz_weak_mixing_of_ergodic (hB : Ergodic B m) : Proposition3Statement := by
  let α : ℝ := 1/51200
  let η : ℝ≥0 := ⟨α/320,by norm_num [α]⟩
  have hα : 0<α := by norm_num [α]
  have hCB := ergodic_compactB hB
  have hsect := compact_bcz_sections α hα
  have hρ : Tendsto (fun n => compactBCZMeasure.real (compactYr (bczScale n α))) atTop (𝓝 1) := by
    simpa only [Measure.real,compactYr_mass] using bczScale_section_mass_tendsto hα
  have hrecNN := reciprocalSectionMass_tendsto compactBCZMeasure (fun n => compactYr (bczScale n α)) hρ
  have hrec : ∀ᶠ n : ℕ in atTop,(compactBCZMeasure (compactYr (bczScale n α)))⁻¹≤(2 : ℝ≥0∞) := by
    filter_upwards [hsect,(hrecNN.eventually (Iio_mem_nhds (by norm_num : (1 : ℝ≥0)<2)))] with n hn hrecn
    rw [← reciprocalSectionMass_coe hn.2.1]
    exact ENNReal.coe_le_coe.mpr hrecn.le
  have hzero : ∀ᶠ n : ℕ in atTop,(3/4 : ℝ≥0)≤
      (excessGraphFinite compactB compactBCZMeasure (compactYr (bczScale n α)) n 0).mass := by
    filter_upwards [bczScale_eventually hα,hsect,compact_small_scale_moment] with n hr hn hm
    have hr0 : 0<bczScale n α := by linarith [hr.1]
    have hh := excessGraph_head_tail_bound hCB hn.1 hn.2.1 (measurePreserving_compactPhi hr0 hr.2)
      (compactPhi_induced_conjugacy hr0 hr.2) n 0 (1/4) hm
    rw [sectionGraph_mass_one measurable_compactB hn.2.1 n] at hh
    norm_num at hh
    have hR : (1 : ℝ)≤((excessGraphFinite compactB compactBCZMeasure (compactYr (bczScale n α)) n 0).mass : ℝ)+1/4 := by
      exact_mod_cast hh
    exact_mod_cast (show (3 : ℝ)/4≤((excessGraphFinite compactB compactBCZMeasure (compactYr (bczScale n α)) n 0).mass : ℝ) by linarith)
  have hone : ∀ᶠ n : ℕ in atTop,η≤
      (excessGraphFinite compactB compactBCZMeasure (compactYr (bczScale n α)) n 1).mass := by
    filter_upwards [bczScale_eventually hα,exactly_one_extra_fixed_of_ergodic hB] with n hr hn
    have hr0 : 0<bczScale n α := by linarith [hr.1]
    exact_mod_cast compact_excess_one_mass_ge hr0 hr.2 n hn
  let Good : ℕ → Prop := fun n => (2 : ℝ)/3<bczScale n α ∧ bczScale n α<1 ∧
    0<compactBCZMeasure (compactYr (bczScale n α)) ∧
    (compactBCZMeasure (compactYr (bczScale n α)))⁻¹≤(2 : ℝ≥0∞) ∧
    (3/4 : ℝ≥0)≤(excessGraphFinite compactB compactBCZMeasure (compactYr (bczScale n α)) n 0).mass ∧
    η≤(excessGraphFinite compactB compactBCZMeasure (compactYr (bczScale n α)) n 1).mass
  have hall : ∀ᶠ n : ℕ in atTop,Good n := by
    filter_upwards [bczScale_eventually hα,hsect,hrec,hzero,hone] with n hr hn hrecn hz ho
    exact ⟨hr.1,hr.2,hn.2.1,hrecn,hz,ho⟩
  obtain ⟨N,hN⟩ := Filter.eventually_atTop.mp hall
  let b := fun n : ℕ => n+N
  have hgood (n : ℕ) : Good (b n) := hN _ (by dsimp [b]; omega)
  have hpos (n : ℕ) : 0<bczScale (b n) α := by have := (hgood n).1; linarith
  apply weakMixing_B_of_compact
  apply weakMixing_of_adjacent_excess_levels hCB
    (fun n => compactYr (bczScale (b n) α)) (fun n => compactPhi (bczScale (b n) α))
    (fun n => measurableSet_compactYr _) (fun n => (hgood n).2.2.1)
    (fun n => measurePreserving_compactPhi (hpos n) (hgood n).2.1)
    (fun n => compactPhi_induced_conjugacy (hpos n) (hgood n).2.1)
    ?_ (hρ.comp (tendsto_add_atTop_nat N)) 2 (fun n => (hgood n).2.2.2.1) b (3/4) η
    (by norm_num) (by exact_mod_cast (show (0 : ℝ)<α/320 by norm_num [α])) (fun n => (hgood n).2.2.2.2.1) (fun n => (hgood n).2.2.2.2.2)
  filter_upwards [ae_compact_mem_Omega] with z hz
  exact (compactPhi_tendsto_pointwise hz).comp ((bczScale_tendsto_left hα).comp (tendsto_add_atTop_nat N))

/-- All mixing proof steps are now discharged once BCZ ergodicity is supplied. -/
theorem bcz_strong_mixing_of_ergodic (hB : Ergodic B m) : Theorem1Statement :=
  bcz_strong_mixing_of_weak_mixing (bcz_weak_mixing_of_ergodic hB)

end
end Paper14
