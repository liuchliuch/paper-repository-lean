import Paper27.Geometry.FibrationBound
import Paper27.Geometry.FormulaSixGeometry

/-!
# The original common-component argument from the original fibrations

The supplementary inputs are universal ordinary Laurent calculus, removal of
actual meromorphic section singularities and ordinary holomorphic bundle
calculus, and factorization into an embedded complex submanifold. They contain
no averaging, principal-part cancellation, invariant splitting, tangency, or
fibration obstruction. The original formula-(6) proof constructs all these
objects and deductions from the three original fibrations.
-/
noncomputable section
namespace Paper27.Geometry

structure AveragingInputs where
  laurent : MeromorphicSplittingAverage.LaurentCalculus
  extension : PuncturedSplittingSections.LaurentSectionExtension laurent
  calculus : PuncturedSplittingSections.HolomorphicPuncturedCalculus
  factorization : HolomorphicEmbeddedFactorization

namespace ClassicalInputs
variable {X : CompactComplexSurface} (K : ClassicalInputs) (Q : AveragingInputs)
include K Q

/-- Lemma 3.3 by its original meromorphic average, beginning with the
original actual maps. No ramification family, retraction, atlas, action,
index, pole, leading coefficient or splitting is supplied as an input. -/
theorem common_tangency_impossible_by_averaging (f g h : Fibration X)
    (hf : f.Smooth) (hg : g.Smooth) (hh : h.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hH : h.Hyperbolic)
    (hnefg : ¬ Fibration.Equivalent f g) (hnefh : ¬ Fibration.Equivalent f h)
    (hnegh : ¬ Fibration.Equivalent g h)
    (D : EmbeddedCurve X) (hD : D.curve.Hyperbolic)
    (hDfg : D.TangentToPair f g) (hDfh : D.TangentToPair f h)
    (hDgh : D.TangentToPair g h) : False := by
  obtain ⟨hfinite12, hsurj12⟩ := K.finite_pair f g hf hg hnefg
  obtain ⟨hfinite13, hsurj13⟩ := K.finite_pair f h hf hh hnefh
  obtain ⟨hfinite23, hsurj23⟩ := K.finite_pair g h hg hh hnegh
  obtain ⟨F⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen f g hf hg hB hC hfinite12 hsurj12
  obtain ⟨E⟩ := RamificationFamilies.ramification_family_exists K.toCurveBranchInputs
    K.submanifolds K.nonsingularOpen f h hf hh hB hH hfinite13 hsurj13
  let p := D.curve.basepoint
  have hsubF : D.support ⊆ F.toDisjointCurveFamily.support := by
    rw [F.support_eq]
    exact hDfg
  have hsubE : D.support ⊆ E.toDisjointCurveFamily.support := by
    rw [E.support_eq]
    exact hDfh
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hsubF ⟨p, rfl⟩)
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp (hsubE ⟨p, rfl⟩)
  have hF := F.toDisjointCurveFamily.component_eq_of_meets Q.factorization
    (FibreGeometry.compactCurveMapTheorem K.curveMaps) D hsubF i p hi
  have hE := E.toDisjointCurveFamily.component_eq_of_meets Q.factorization
    (FibreGeometry.compactCurveMapTheorem K.curveMaps) D hsubE j p hj
  have hu12 := K.unramified_tangent f g hf hg hB hC hfinite12 hsurj12 D hDfg
  have hu13 := K.unramified_tangent f h hf hh hB hH hfinite13 hsurj13 D hDfh
  let R := CommonRetractions.triple K.unramifiedCurveCovering K.neighbourhoodLifting
    K.etaleLiftRegularity D f g h hu12.1 hu12.2 hu13.2
  obtain ⟨n, hn, ⟨A⟩⟩ := K.normal_atlas f g hf hg hB hC hfinite12 hsurj12 hDfg
    R.first_factor R.second_factor
  obtain ⟨m, hm, ⟨B⟩⟩ := K.normal_atlas f h hf hh hB hH hfinite13 hsurj13 hDfh
    R.first_factor R.third_factor
  obtain ⟨k, hk, ⟨C⟩⟩ := K.normal_atlas g h hg hh hC hH hfinite23 hsurj23 hDgh
    R.second_factor R.third_factor
  exact FormulaSixGeometry.impossible K.taylor K.parameterTaylor Q.laurent Q.extension
    Q.calculus K.normalDivision K.mapGermGluing K.normalFrames K.degreeTheory
    K.degreeGaugeInvariance K.bott f g h F E i j hF hE A B C hn hm hk
    hu12.1 hu12.2 hu13.2 R.first_factor R.second_factor R.third_factor hD

end ClassicalInputs
end Paper27.Geometry
