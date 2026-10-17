import Paper29.GeneralInformation
import Mathlib.Topology.Constructions.SumProd

noncomputable section
open MeasureTheory
namespace Paper29

/-- The existing measurable disjoint sum agrees with the Borel disjoint sum. -/
instance sumBorelSpace {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    [MeasurableSpace A] [MeasurableSpace B] [BorelSpace A] [BorelSpace B] : BorelSpace (A ⊕ B) := by
  constructor
  apply le_antisymm
  · intro D hD
    have hm := measurableSet_sum_iff.mp hD
    let mB := borel (A ⊕ B)
    letI : @BorelSpace (A ⊕ B) _ mB := ⟨rfl⟩
    have hl : MeasurableSet[mB] (Sum.inl '' (Sum.inl ⁻¹' D)) :=
      Topology.IsClosedEmbedding.inl.measurableEmbedding.measurableSet_image.mpr hm.1
    have hr : MeasurableSet[mB] (Sum.inr '' (Sum.inr ⁻¹' D)) :=
      Topology.IsClosedEmbedding.inr.measurableEmbedding.measurableSet_image.mpr hm.2
    have he : Sum.inl '' (Sum.inl ⁻¹' D) ∪ Sum.inr '' (Sum.inr ⁻¹' D)=D := by
      ext x
      cases x <;> simp
    rw [← he]
    exact hl.union hr
  · apply MeasurableSpace.generateFrom_le
    intro D hD
    exact measurableSet_sum_iff.mpr ⟨(hD.preimage continuous_inl).measurableSet,
      (hD.preimage continuous_inr).measurableSet⟩

end Paper29
