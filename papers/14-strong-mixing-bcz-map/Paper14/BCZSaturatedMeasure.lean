import Paper14.BCZQuotientMeasure

open MeasureTheory Measure Filter Set Topology Function
open scoped ENNReal Matrix
namespace Paper14
noncomputable section
open Background

def bczSaturatedSet (A : Set (ℝ × ℝ)) : Set LatticeSpace :=
  QuotientGroup.mk '' slBczSuspensionOver A

lemma measurableSet_bczSaturatedSet {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    MeasurableSet (bczSaturatedSet A) :=
  (measurableSet_slBczSuspensionOver hA).image_of_measurable_injOn
    measurePreserving_latticeProjection.measurable
    (slBczFundamental_quotient_injOn.mono slBczSuspensionOver_subset)

lemma latticeProjection_saturated_preimage (A : Set (ℝ × ℝ)) :
    (QuotientGroup.mk : SL2R → LatticeSpace) ⁻¹' bczSaturatedSet A ∩
      slBczSuspensionOver univ=slBczSuspensionOver A := by
  ext g
  constructor
  · rintro ⟨⟨h,hh,hq⟩,hg⟩
    have heq := slBczFundamental_quotient_injOn (slBczSuspensionOver_subset hh) hg hq
    simpa only [heq] using hh
  · intro hg
    exact ⟨⟨g,hg,rfl⟩,slBczSuspensionOver_subset hg⟩

lemma slBczSuspensionOver_compl (A : Set (ℝ × ℝ)) :
    slBczSuspensionOver Aᶜ=slBczSuspensionOver univ \ slBczSuspensionOver A := by
  ext g
  simp only [slBczSuspensionOver,bczSuspensionOver,mem_preimage,mem_setOf_eq,mem_inter_iff,
    mem_compl_iff,mem_univ,true_and,and_true,mem_diff]
  tauto

lemma latticeProjection_saturated_compl_preimage (A : Set (ℝ × ℝ)) :
    (QuotientGroup.mk : SL2R → LatticeSpace) ⁻¹' (bczSaturatedSet A)ᶜ ∩
      slBczSuspensionOver univ=slBczSuspensionOver Aᶜ := by
  rw [slBczSuspensionOver_compl,← latticeProjection_saturated_preimage A]
  ext g
  simp <;> tauto

lemma latticeMeasure_bczSaturatedSet {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    latticeMeasure (bczSaturatedSet A)=∫⁻ x in Omega ∩ A,ENNReal.ofReal (tau x) := by
  rw [latticeMeasure,Measure.map_apply measurePreserving_latticeProjection.measurable (measurableSet_bczSaturatedSet hA),
    Measure.restrict_apply (measurePreserving_latticeProjection.measurable (measurableSet_bczSaturatedSet hA)),
    latticeProjection_saturated_preimage]
  exact slFlatMeasure_bczSuspensionOver hA

lemma latticeMeasure_bczSaturatedSet_compl {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    latticeMeasure (bczSaturatedSet A)ᶜ=∫⁻ x in Omega ∩ Aᶜ,ENNReal.ofReal (tau x) := by
  rw [latticeMeasure,Measure.map_apply measurePreserving_latticeProjection.measurable (measurableSet_bczSaturatedSet hA).compl,
    Measure.restrict_apply (measurePreserving_latticeProjection.measurable (measurableSet_bczSaturatedSet hA).compl),
    latticeProjection_saturated_compl_preimage]
  exact slFlatMeasure_bczSuspensionOver hA.compl

lemma section_measure_le_suspension {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    m A≤2*(∫⁻ x in Omega ∩ A,ENNReal.ofReal (tau x)) := by
  have hlower : volume (Omega ∩ A)≤∫⁻ x in Omega ∩ A,ENNReal.ofReal (tau x) := by
    calc
      volume (Omega ∩ A)=(∫⁻ _x in Omega ∩ A,(1 : ℝ≥0∞)) := by simp
      _ ≤ _ := by
        apply lintegral_mono_ae
        filter_upwards [ae_restrict_mem (measurableSet_Omega.inter hA)] with x hx
        simpa using ENNReal.ofReal_le_ofReal (tau_ge_one hx.1)
  have heq : m A=(2 : ℝ≥0∞)*volume (Omega ∩ A) := by
    rw [m,Measure.smul_apply,smul_eq_mul,Measure.restrict_apply hA,inter_comm]
  rw [heq]
  exact mul_le_mul_left' hlower 2

/-- A zero or full suspension event forces the corresponding actual BCZ section event. -/
theorem section_aeconst_of_saturated_aeconst {A : Set (ℝ × ℝ)} (hA : MeasurableSet A)
    (hconst : EventuallyConst (bczSaturatedSet A) (ae latticeMeasure)) : EventuallyConst A (ae m) := by
  rw [eventuallyConst_set] at hconst ⊢
  rcases hconst with hfull | hzero
  · left
    have hz : latticeMeasure (bczSaturatedSet A)ᶜ=0 := by
      simpa only [ae_iff,not_not] using hfull
    have hm : m Aᶜ=0 := by
      apply le_zero_iff.mp
      calc
        m Aᶜ≤2*(∫⁻ x in Omega ∩ Aᶜ,ENNReal.ofReal (tau x)) := section_measure_le_suspension hA.compl
        _ = 0 := by rw [← latticeMeasure_bczSaturatedSet_compl hA,hz,mul_zero]
    exact ae_iff.mpr hm
  · right
    have hz : latticeMeasure (bczSaturatedSet A)=0 := by
      simpa only [ae_iff,not_not] using hzero
    have hm : m A=0 := by
      apply le_zero_iff.mp
      calc
        m A≤2*(∫⁻ x in Omega ∩ A,ENNReal.ofReal (tau x)) := section_measure_le_suspension hA
        _ = 0 := by rw [← latticeMeasure_bczSaturatedSet hA,hz,mul_zero]
    simpa only [ae_iff,not_not] using hm

end
end Paper14
