import Paper14.CompactBCZ

open MeasureTheory Set Function Filter Topology
namespace Paper14
noncomputable section

def compactYr (r : ℝ) : Set CompactBCZ := Subtype.val ⁻¹' Yr r

lemma measurableSet_compactYr (r : ℝ) : MeasurableSet (compactYr r) := measurable_subtype_coe (measurableSet_Yr r)

lemma compactYr_mass (r : ℝ) : compactBCZMeasure (compactYr r) = m (Yr r) :=
  measurePreserving_compactCoe.measure_preimage (measurableSet_Yr r).nullMeasurableSet

lemma compactB_iterate_coe {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) (n : ℕ) :
    ((compactB^[n] z : CompactBCZ) : ℝ × ℝ) = B^[n] z.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    have hn : ((compactB^[n] z : CompactBCZ) : ℝ × ℝ) ∈ Omega := by rw [ih]; exact B_iterate_mem hz n
    rw [compactB_coe hn,ih,iterate_succ_apply']

lemma compact_firstReturn_eq {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) (r : ℝ) :
    firstReturnTime compactB (compactYr r) z = firstReturnTime B (Yr r) z.val := by
  have hiff (n : ℕ) : compactB^[n] z ∈ compactYr r ↔ B^[n] z.val ∈ Yr r := by
    change ((compactB^[n] z : CompactBCZ) : ℝ × ℝ) ∈ Yr r ↔ _
    rw [compactB_iterate_coe hz]
  by_cases hb : ∃ n, 0 < n ∧ B^[n] z.val ∈ Yr r
  · have hc : ∃ n, 0 < n ∧ compactB^[n] z ∈ compactYr r := by
      obtain ⟨n,hn,hm⟩ := hb
      exact ⟨n,hn,(hiff n).mpr hm⟩
    have hsB := firstReturn_spec hb
    have hsC := firstReturn_spec hc
    exact Nat.le_antisymm (firstReturn_le hsB.1 ((hiff _).mpr hsB.2))
      (firstReturn_le hsC.1 ((hiff _).mp hsC.2))
  · have hc : ¬ ∃ n, 0 < n ∧ compactB^[n] z ∈ compactYr r := by
      rintro ⟨n,hn,hm⟩
      exact hb ⟨n,hn,(hiff n).mp hm⟩
    rw [firstReturnTime_of_not_exists hb,firstReturnTime_of_not_exists hc]

lemma compact_induced_coe {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) (r : ℝ) :
    ((inducedMap compactB (compactYr r) z : CompactBCZ) : ℝ × ℝ) = inducedMap B (Yr r) z.val := by
  unfold inducedMap
  rw [compactB_iterate_coe hz,compact_firstReturn_eq hz]

lemma compact_induced_iterate_coe {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) (r : ℝ) (n : ℕ) :
    (((inducedMap compactB (compactYr r))^[n] z : CompactBCZ) : ℝ × ℝ) =
      (inducedMap B (Yr r))^[n] z.val := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_apply']
    have hm : (((inducedMap compactB (compactYr r))^[n] z : CompactBCZ) : ℝ × ℝ) ∈ Omega := by
      rw [ih,induced_iterate_eq]
      exact B_iterate_mem hz _
    rw [compact_induced_coe hm,ih,iterate_succ_apply']

lemma compact_Rn_eq {z : CompactBCZ} (hz : (z : ℝ × ℝ) ∈ Omega) (r : ℝ) (n : ℕ) :
    Rn compactB (compactYr r) n z = Rn B (Yr r) n z.val := by
  unfold Rn
  apply Finset.sum_congr rfl
  intro i hi
  have hm : (((inducedMap compactB (compactYr r))^[i] z : CompactBCZ) : ℝ × ℝ) ∈ Omega := by
    rw [compact_induced_iterate_coe hz,induced_iterate_eq]
    exact B_iterate_mem hz _
  rw [compact_firstReturn_eq hm,compact_induced_iterate_coe hz]

/-- Strong mixing on the compact carrier transfers to the original actual
BCZ map and its original measure. -/
theorem strongMixing_B_of_compact (hmix : StrongMixing compactB compactBCZMeasure) : StrongMixing B m := by
  intro A C hA hC
  have hh := hmix (Subtype.val ⁻¹' A) (Subtype.val ⁻¹' C)
    (measurable_subtype_coe hA) (measurable_subtype_coe hC)
  have hmass (A : Set (ℝ × ℝ)) (hA : MeasurableSet A) : compactBCZMeasure (Subtype.val ⁻¹' A) = m A :=
    measurePreserving_compactCoe.measure_preimage hA.nullMeasurableSet
  rw [hmass A hA,hmass C hC] at hh
  have htest (n : ℕ) : compactBCZMeasure ((compactB^[n]) ⁻¹' (Subtype.val ⁻¹' A) ∩ (Subtype.val ⁻¹' C)) =
      m ((B^[n]) ⁻¹' A ∩ C) := by
    rw [← hmass ((B^[n]) ⁻¹' A ∩ C) (((measurable_B.iterate n) hA).inter hC)]
    apply measure_congr
    filter_upwards [ae_compact_mem_Omega] with z hz
    apply propext
    change (((compactB^[n] z : CompactBCZ) : ℝ × ℝ) ∈ A ∧ z.val ∈ C) ↔ (B^[n] z.val ∈ A ∧ z.val ∈ C)
    rw [compactB_iterate_coe hz]
  simpa only [htest] using hh

end
end Paper14
