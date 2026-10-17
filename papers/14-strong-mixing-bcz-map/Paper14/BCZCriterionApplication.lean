import Paper14.BCZExcessHypotheses
import Paper14.ExcessCriterionProof

open MeasureTheory Set Function Filter Topology
namespace Paper14
noncomputable section

lemma compact_bcz_sections : ∀ α : ℝ, 0 < α → ∀ᶠ n : ℕ in atTop,
    MeasurableSet (compactYr (bczScale n α)) ∧ 0 < compactBCZMeasure (compactYr (bczScale n α)) ∧
      (bczScale n α)^2 = (compactBCZMeasure (compactYr (bczScale n α))).toReal := by
  intro α hα
  filter_upwards [bczScale_eventually hα] with n hn
  have hr : 0 < bczScale n α := by linarith [hn.1]
  refine ⟨measurableSet_compactYr _,?_,?_⟩
  · rw [compactYr_mass,m_Yr hr hn.2]
    exact ENNReal.ofReal_pos.mpr (sq_pos_of_pos hr)
  · rw [compactYr_mass,m_Yr hr hn.2,ENNReal.toReal_ofReal (sq_nonneg _)]

lemma compact_bcz_conjNearId : ConjNearId compactB compactBCZMeasure
    (fun n α => compactYr (bczScale n α)) (fun n α => compactPhi (bczScale n α)) := by
  intro α hα
  refine ⟨?_,compactPhi_tendstoInMeasure _ (bczScale_tendsto_left hα)⟩
  filter_upwards [bczScale_eventually hα] with n hn
  have hr : 0 < bczScale n α := by linarith [hn.1]
  have hi := compactPhi_inverse_ae hr hn.2
  exact ⟨measurePreserving_compactPhi hr hn.2,
    ⟨compactPhiInv _,measurable_compactPhiInv _,hi.1,hi.2⟩,compactPhi_induced_conjugacy hr hn.2⟩

lemma compact_zero_event_preimage (r : ℝ) (n : ℕ) :
    {z ∈ compactYr r | Rn compactB (compactYr r) n z = n} =
      (Subtype.val : CompactBCZ → ℝ × ℝ) ⁻¹' {x ∈ Yr r | Rn B (Yr r) n x = n} := by
  ext z
  constructor
  · rintro ⟨hz,hn⟩
    refine ⟨hz,?_⟩
    rw [← compact_Rn_eq hz.1 r n]
    exact hn
  · rintro ⟨hz,hn⟩
    refine ⟨hz,?_⟩
    rw [compact_Rn_eq hz.1 r n]
    exact hn

lemma compact_bcz_zeroExcessSmall (hB : Ergodic B m) :
    ZeroExcessSmall compactB compactBCZMeasure (fun n α => compactYr (bczScale n α))
      (fun n α => (bczScale n α)^2) := by
  intro ε hε
  obtain ⟨α0,hα0⟩ := bcz_zeroExcessSmall hB ε hε
  refine ⟨max α0 0,?_⟩
  intro α hαbig
  have hα : 0 < α := lt_of_le_of_lt (le_max_right α0 0) hαbig
  obtain ⟨Nz,hNz⟩ := hα0 α (lt_of_le_of_lt (le_max_left α0 0) hαbig)
  apply Filter.eventually_atTop.mp
  filter_upwards [bczScale_eventually hα,eventually_ge_atTop Nz] with n hn hnn
  have hr : 0 < bczScale n α := by linarith [hn.1]
  have hE : MeasurableSet {x ∈ Yr (bczScale n α) | Rn B (Yr (bczScale n α)) n x = n} :=
    (measurableSet_Yr _).inter ((measurable_Rn measurable_B (measurableSet_Yr _) n) (measurableSet_singleton n))
  rw [compact_zero_event_preimage,
    (measurePreserving_compactCoe_section hr hn.2).measure_preimage hE.nullMeasurableSet,
    mr_eq_normalizedRestriction hr hn.2]
  exact hNz n hnn

/-- All source self-induction, scale, zero-excess and compact-model steps
are proved. Only the original weak-mixing proposition remains an input. -/
theorem bcz_strong_mixing_of_weak_mixing (hweak : WeakMixing B m) : Theorem1Statement := by
  have hB : Ergodic B m := ⟨hweak.1,
    (measurePreserving_fst (μ := m) (ν := m)).preErgodic_of_preErgodic_conjugate
      hweak.2.toPreErgodic (fun p => rfl)⟩
  apply strongMixing_B_of_compact
  exact Theorem4 compactB compactBCZMeasure (fun n α => compactYr (bczScale n α))
    (fun n α => compactPhi (bczScale n α)) (fun n α => (bczScale n α)^2)
    (by infer_instance)
    ⟨compactBinv,measurable_compactBinv,compact_inverse_ae.1,compact_inverse_ae.2⟩
    measurePreserving_compactB (weakMixing_compactB hweak) compact_bcz_sections compact_bcz_conjNearId
    bcz_excess_moment (compact_bcz_zeroExcessSmall hB)

end
end Paper14
