import Paper14.ExactlyOneFixed
import Paper14.BCZCriterionApplication

open MeasureTheory Filter Topology Set Function
open scoped NNReal ENNReal
namespace Paper14
noncomputable section

lemma ergodic_compactB (hB : Ergodic B m) : Ergodic compactB compactBCZMeasure :=
  ergodic_of_ae_factor hB measurePreserving_compactClamp measurable_compactB compactB_ae_factor

lemma weakMixing_B_of_compact (hw : WeakMixing compactB compactBCZMeasure) : WeakMixing B m := by
  refine ⟨measurePreserving_B,?_⟩
  apply ergodic_of_ae_factor hw.2 (measurePreserving_compactCoe.prod measurePreserving_compactCoe)
    (measurable_B.prodMap measurable_B)
  filter_upwards [(measurePreserving_fst (μ := compactBCZMeasure) (ν := compactBCZMeasure)).quasiMeasurePreserving.ae ae_compact_mem_Omega,
    (measurePreserving_snd (μ := compactBCZMeasure) (ν := compactBCZMeasure)).quasiMeasurePreserving.ae ae_compact_mem_Omega] with z hz hq
  exact Prod.ext (compactB_coe hz) (compactB_coe hq)

lemma compact_excess_one_event_preimage (r : ℝ) (n : ℕ) :
    excessLevel compactB (compactYr r) n 1=
      (Subtype.val : CompactBCZ → ℝ × ℝ) ⁻¹' {x ∈ Yr r | Rn B (Yr r) n x=n+1} := by
  ext z
  constructor
  · rintro ⟨hz,hD⟩
    refine ⟨hz,?_⟩
    rw [← compact_Rn_eq hz.1 r n]
    change Rn compactB (compactYr r) n z-n=1 at hD
    omega
  · rintro ⟨hz,hR⟩
    refine ⟨hz,?_⟩
    change Rn compactB (compactYr r) n z-n=1
    rw [compact_Rn_eq hz.1 r n]
    omega

lemma compact_excess_one_mass_ge {r : ℝ} (hr : 0<r) (hr1 : r<1) (n : ℕ) {η : ℝ}
    (hη : η≤(m {x ∈ Yr r | Rn B (Yr r) n x=n+1}).toReal) :
    η≤((excessGraphFinite compactB compactBCZMeasure (compactYr r) n 1).mass : ℝ) := by
  let E := {x ∈ Yr r | Rn B (Yr r) n x=n+1}
  have hE : MeasurableSet E := (measurableSet_Yr r).inter
    ((measurable_Rn measurable_B (measurableSet_Yr r) n) (measurableSet_singleton (n+1)))
  have hp : 0<m (Yr r) := by rw [m_Yr hr hr1]; exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)
  letI : IsProbabilityMeasure (mr r) := by
    rw [mr_eq_normalizedRestriction hr hr1]
    exact normalizedRestriction_probability hp.ne'
  have hmass : m E≤mr r E := by
    rw [mr_eq_normalizedRestriction hr hr1,normalizedRestriction,Measure.smul_apply,smul_eq_mul,
      Measure.restrict_apply hE,inter_eq_self_of_subset_left (show E⊆Yr r from fun x hx => hx.1)]
    exact le_mul_of_one_le_left' (ENNReal.one_le_inv.mpr MeasureTheory.prob_le_one)
  have hηr : η≤(mr r E).toReal := hη.trans (ENNReal.toReal_mono (measure_ne_top _ _) hmass)
  have hm := excessGraph_mass measurable_compactB compactBCZMeasure (compactYr r) n 1
  rw [compact_excess_one_event_preimage,
    (measurePreserving_compactCoe_section hr hr1).measure_preimage hE.nullMeasurableSet] at hm
  have hmR := congrArg ENNReal.toReal hm
  exact hηr.trans_eq hmR.symm

lemma compact_small_scale_moment :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)*((compactBCZMeasure (compactYr (bczScale n (1/51200)))).toReal⁻¹-1)≤1/4 := by
  let α : ℝ := 1/51200
  have hα : 0<α := by norm_num [α]
  have hlim : Tendsto (fun n : ℕ => (n : ℝ)*((compactBCZMeasure (compactYr (bczScale n α))).toReal⁻¹-1))
      atTop (𝓝 (2*α)) := by
    have ht := scaleLimit hα
    simp only [Real.rpow_two] at ht
    apply (tendsto_congr' ?_).mpr ht
    filter_upwards [bczScale_eventually hα] with n hn
    have hr : 0<bczScale n α := by linarith [hn.1]
    rw [compactYr_mass,m_Yr hr hn.2,ENNReal.toReal_ofReal (sq_nonneg _)]
    rfl
  exact (hlim.eventually (Iio_mem_nhds (show 2*α<(1 : ℝ)/4 by norm_num [α]))).mono (fun _ hn => hn.le)

end
end Paper14
