import Paper14.LatticeQuotient
import Paper14.RoofMean
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory Measure Filter Set Topology Function
open scoped ENNReal Matrix
namespace Paper14
noncomputable section
open Background

/-- Coordinates group the section point (a,b) and the actual horocycle time. -/
def suspensionCoordinates : SL2Coordinates ≃ᵐ ((ℝ × ℝ) × ℝ) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).trans
    ((MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ)
      (MeasurableEquiv.piFinTwo (fun _ : Fin 2 => ℝ))).trans MeasurableEquiv.prodComm)

lemma suspensionCoordinates_apply (z : SL2Coordinates) :
    suspensionCoordinates z=((z 0,z 1),z 2) := rfl

lemma measurePreserving_suspensionCoordinates : MeasurePreserving suspensionCoordinates volume volume := by
  exact measurePreserving_swap.comp
    (((MeasurePreserving.id (volume : Measure ℝ)).prod
      (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ))).comp
      (volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2))

/-- The part of the BCZ suspension above a specified section set. -/
def bczSuspensionOver (A : Set (ℝ × ℝ)) : Set ((ℝ × ℝ) × ℝ) :=
  {p | p.1∈Omega ∩ A ∧ 0≤p.2 ∧ p.2<tau p.1}

lemma measurableSet_bczSuspensionOver {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    MeasurableSet (bczSuspensionOver A) := by
  have hτ : Measurable tau := by unfold tau; fun_prop
  exact (measurable_fst (measurableSet_Omega.inter hA)).inter
    ((measurableSet_le measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd (hτ.comp measurable_fst)))

/-- The identical roof domain inside the actual matrix group. -/
def slBczSuspensionOver (A : Set (ℝ × ℝ)) : Set SL2R :=
  (fun g => suspensionCoordinates (slCoordinates g)) ⁻¹' bczSuspensionOver A

lemma measurableSet_slBczSuspensionOver {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    MeasurableSet (slBczSuspensionOver A) :=
  (measurableSet_bczSuspensionOver hA).preimage
    (suspensionCoordinates.measurable.comp measurable_slCoordinates)

lemma volume_bczSuspensionOver {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    volume (bczSuspensionOver A)=∫⁻ x in Omega ∩ A,ENNReal.ofReal (tau x) := by
  change (volume.prod volume) (bczSuspensionOver A)=_
  rw [Measure.prod_apply (measurableSet_bczSuspensionOver hA)]
  have heq : (fun x : ℝ × ℝ => volume (Prod.mk x ⁻¹' bczSuspensionOver A))=
      (Omega ∩ A).indicator (fun x => ENNReal.ofReal (tau x)) := by
    funext x
    by_cases hx : x∈Omega ∩ A
    · have hset : Prod.mk x ⁻¹' bczSuspensionOver A=Ico 0 (tau x) := by
        ext t
        simp only [bczSuspensionOver,mem_preimage,mem_setOf_eq,mem_Ico]
        exact and_iff_right hx
      rw [hset,Real.volume_Ico,sub_zero,indicator_of_mem hx]
    · have hset : Prod.mk x ⁻¹' bczSuspensionOver A=∅ := by
        ext t
        simp only [bczSuspensionOver,mem_preimage,mem_setOf_eq,hx,false_and,mem_empty_iff_false]
      rw [hset,measure_empty,indicator_of_notMem hx]
  rw [heq,lintegral_indicator (measurableSet_Omega.inter hA)]

/-- The constructed invariant group measure has exactly the source section/flow density. -/
theorem slFlatMeasure_bczSuspensionOver {A : Set (ℝ × ℝ)} (hA : MeasurableSet A) :
    slFlatMeasure (slBczSuspensionOver A)=∫⁻ x in Omega ∩ A,ENNReal.ofReal (tau x) := by
  rw [slFlatMeasure,Measure.map_apply measurable_slChart (measurableSet_slBczSuspensionOver hA)]
  calc
    volume (slChart ⁻¹' slBczSuspensionOver A)=
        volume (suspensionCoordinates ⁻¹' bczSuspensionOver A) := by
      apply measure_congr
      filter_upwards [ae_slCoordinate_ne 0 0] with z hz
      change (suspensionCoordinates (slCoordinates (slChart z))∈bczSuspensionOver A)=
        (suspensionCoordinates z∈bczSuspensionOver A)
      rw [slCoordinates_chart hz]
    _ = volume (bczSuspensionOver A) :=
      measurePreserving_suspensionCoordinates.measure_preimage
        (measurableSet_bczSuspensionOver hA).nullMeasurableSet
    _ = _ := volume_bczSuspensionOver hA

/-- The actual BCZ roof domain has finite group measure. -/
theorem slFlatMeasure_bczSuspension_finite : slFlatMeasure (slBczSuspensionOver univ)<⊤ := by
  rw [slFlatMeasure_bczSuspensionOver MeasurableSet.univ,inter_univ]
  have hon : IntegrableOn tau Omega :=
    (integrable_smul_measure (by norm_num : (2 : ENNReal)≠0)
      (by norm_num : (2 : ENNReal)≠⊤)).mp integrable_tau
  exact lt_of_le_of_lt (lintegral_mono (fun x => Real.ofReal_le_enorm (tau x))) hon.2

end
end Paper14
