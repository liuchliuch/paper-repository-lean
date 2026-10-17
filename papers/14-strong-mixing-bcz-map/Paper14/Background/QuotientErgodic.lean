import Mathlib.Dynamics.Ergodic.Action.Regular
import Mathlib.MeasureTheory.Measure.Haar.Quotient

open MeasureTheory Measure Filter Set Topology
namespace Paper14.Background
noncomputable section

/-- The homogeneous group action on a quotient equipped with the measure of
any fundamental domain is ergodic. -/
theorem quotient_ergodicSMul
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] [MeasurableMul₂ G] [MeasurableInv G] {Γ : Subgroup G} [Countable Γ]
    [MeasurableSpace (G ⧸ Γ)] [BorelSpace (G ⧸ Γ)]
    {ν : Measure G} [ν.IsMulLeftInvariant] [ν.IsMulRightInvariant] [SFinite ν]
    {F : Set G} (hF : IsFundamentalDomain Γ.op F ν)
    {μ : Measure (G ⧸ Γ)} [SMulInvariantMeasure G (G ⧸ Γ) μ]
    (hq : MeasurePreserving (QuotientGroup.mk : G → G ⧸ Γ) (ν.restrict F) μ) :
    ErgodicSMul G (G ⧸ Γ) μ := by
  let q : G → G ⧸ Γ := QuotientGroup.mk
  have hqm : Measurable q := continuous_quotient_mk'.measurable
  have hac : Measure.map q ν ≪ μ := by
    rw [← hq.map_eq]
    exact hF.absolutelyContinuous_map
  have hqp : QuasiMeasurePreserving q ν μ := ⟨hqm,hac⟩
  refine ⟨fun {s} hs hinv => ?_⟩
  have hall : ∀ g : G,(fun x : G => g*x) ⁻¹' (q ⁻¹' s) =ᵐ[ν] q ⁻¹' s := by
    intro g
    exact hqp.ae (hinv g)
  have hc : EventuallyConst (q ⁻¹' s) (ae ν) :=
    aeconst_of_forall_preimage_smul_ae_eq G (hqm hs).nullMeasurableSet hall
  rw [eventuallyConst_set] at hc ⊢
  rcases hc with h | h
  · left
    rw [← hq.map_eq]
    exact (ae_map_iff hqm.aemeasurable hs).mpr
      (h.filter_mono Measure.absolutelyContinuous_restrict.ae_le)
  · right
    rw [← hq.map_eq]
    exact (ae_map_iff hqm.aemeasurable hs.compl).mpr
      (h.filter_mono Measure.absolutelyContinuous_restrict.ae_le)

end
end Paper14.Background
