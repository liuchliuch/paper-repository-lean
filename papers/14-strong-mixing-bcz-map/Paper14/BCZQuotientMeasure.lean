import Paper14.BCZFundamentalDomain
import Paper14.Background.QuotientErgodic
import Mathlib.Topology.Metrizable.Urysohn
import Mathlib.MeasureTheory.Measure.RegularityCompacts

open MeasureTheory Measure Filter Set Topology Function TopologicalSpace
open scoped ENNReal Matrix
namespace Paper14
noncomputable section
open Background

abbrev LatticeSpace := SL2R ⧸ slIntegerSubgroup
instance : MeasurableSpace LatticeSpace := Quotient.instMeasurableSpace
instance : BorelSpace LatticeSpace := CosetSpace.borelSpace

/-- The actual finite invariant measure obtained from the BCZ roof domain. -/
def latticeMeasure : Measure LatticeSpace :=
  Measure.map QuotientGroup.mk (slFlatMeasure.restrict (slBczSuspensionOver univ))

instance : IsFiniteMeasure (slFlatMeasure.restrict (slBczSuspensionOver univ)) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact slFlatMeasure_bczSuspension_finite⟩

instance : IsFiniteMeasure latticeMeasure := by unfold latticeMeasure; infer_instance

instance : HasFundamentalDomain slIntegerSubgroup.op SL2R slFlatMeasure :=
  ⟨slBczSuspensionOver univ,bcz_suspension_fundamentalDomain⟩

instance : QuotientMeasureEqMeasurePreimage (G := slIntegerSubgroup.op) slFlatMeasure latticeMeasure :=
  bcz_suspension_fundamentalDomain.quotientMeasureEqMeasurePreimage_quotientMeasure

instance : SMulInvariantMeasure SL2R LatticeSpace latticeMeasure :=
  QuotientMeasureEqMeasurePreimage.smulInvariantMeasure_quotient slFlatMeasure

lemma measurePreserving_latticeProjection :
    MeasurePreserving (QuotientGroup.mk : SL2R → LatticeSpace)
      (slFlatMeasure.restrict (slBczSuspensionOver univ)) latticeMeasure :=
  ⟨(show Continuous (QuotientGroup.mk : SL2R → LatticeSpace) from QuotientGroup.continuous_mk).measurable,rfl⟩

instance : ErgodicSMul SL2R LatticeSpace latticeMeasure :=
  quotient_ergodicSMul bcz_suspension_fundamentalDomain measurePreserving_latticeProjection

instance : PseudoMetrizableSpace LatticeSpace := inferInstance
instance : SigmaCompactSpace LatticeSpace := inferInstance
instance : latticeMeasure.InnerRegularCompactLTTop := inferInstance

/-- Horocycle-invariant measurable sets in the actual lattice quotient are null or conull. -/
theorem lattice_horocycle_aeconst {E : Set LatticeSpace} (hE : MeasurableSet E)
    (hL : ∀ t : ℝ,(fun p : LatticeSpace => slLower t • p) ⁻¹' E =ᵐ[latticeMeasure] E) :
    EventuallyConst E (ae latticeMeasure) :=
  aeconst_of_forall_preimage_smul_ae_eq SL2R hE.nullMeasurableSet (slLower_ae_invariant_all hE hL)

end
end Paper14
