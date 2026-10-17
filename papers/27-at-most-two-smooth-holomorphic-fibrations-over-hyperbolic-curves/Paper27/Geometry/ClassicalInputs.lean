import Paper27.Geometry.RamificationFamilies
import Paper27.Geometry.ActualDisjointObstruction
import Paper27.Geometry.FibreGeometry
import Paper27.Geometry.CommonRetractions
import Paper27.Geometry.RetractionNormalCoordinates

/-!
# The explicit universal classical parameters of the relative paper proof

The fields group the precise general interfaces already documented in their
defining modules. There are no actual pair geometries, third-fibration
obstructions, retraction atlases, component tensors or fibration bounds among
these parameters. All those are constructed by the own proof chain.

This is a relative proof interface. It neither asserts these fields as Lean
axioms nor constructs the external theories. The source/dependency ledger
records their mathematical sources and their remaining formalization status.
-/
noncomputable section
namespace Paper27.Geometry

structure ClassicalInputs extends CurveBranchInputs where
  fibreModels : FibreGeometry.SmoothProperFibreModels
  fibreDegrees : FibreGeometry.EhresmannDegreeInvariance curveMaps
  localSections : HolomorphicSubmersionSections
  inverseCurveMap : BijectiveHolomorphicInverse
  submanifolds : SmoothCurveDecomposition.EmbeddedSubmanifoldDecomposition
  nonsingularOpen : RetractionFactorization.NonsingularJointLocusOpen
  localDegrees : RamificationIndexConstancy.FiniteLocalDegreeTheory
  unramifiedCurveCovering : RetractionFactorization.CompactUnramifiedCurveCovering
  neighbourhoodLifting : RetractionFactorization.TopologicalCoverNeighbourhoodLifting
  etaleLiftRegularity : RetractionFactorization.HolomorphicEtaleLiftRegularity
  dividedDifferences : RetractionNormalCoordinates.AnalyticDividedDifferences
  localUnitRoots : RetractionNormalCoordinates.AnalyticUnitRoots
  normalDivision : NormalAtlasAction.HolomorphicNormalDivision
  mapGermGluing : NormalAtlasAction.HolomorphicOpenGermGluing
  normalFrames : ThreePairNormalObstruction.NormalFrameExistence
  frameCalculus : EmbeddedFrames.HolomorphicFrameCalculus
  degreeTheory : LineBundleDegreeTheory
  degreeGaugeInvariance : NormalDegreeInvariance.LineBundleDegreeGaugeInvariance degreeTheory
  homDegree : HomDegreeLaw degreeTheory
  splittingCalculus : NeighbourhoodSplittings.HolomorphicSplittingCalculus
  bott : NeighbourhoodSplittings.BottTangentialSubbundleDegreeZero degreeTheory
  taylor : TaylorGerms.TaylorCalculus
  parameterTaylor : RetractionCoefficientHolomorphic.ParametricTaylorCalculus taylor
  unramifiedSurfaceCovering : RamificationSupport.ProperHolomorphicLocalDiffeomorphismCovering
  productRigidity : ProductCurveRigidity
  productCovers : ProductCoverExistence
  fibreConstancy : ConnectedFibreDerivativeConstancy

namespace ClassicalInputs
variable {X : CompactComplexSurface} (K : ClassicalInputs)
include K

theorem finite_pair (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hne : ¬ Fibration.Equivalent f g) : f.FinitePair g ∧ f.PairSurjective g :=
  FibreGeometry.finitePair_pairSurjective K.curveMaps K.fibreModels K.fibreDegrees
    K.localSections K.inverseCurveMap f g hf hg hne

include K
/-- The empty-ramification branch of the main argument, for original actual
maps. The third map need not be smooth, as required in Lemma 3.4. -/
theorem third_equivalent_of_empty (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (hne : ¬ Fibration.Equivalent f g)
    (hempty : RamificationSupport.ramificationSet f g = ∅)
    (h : Fibration X) (hH : h.Hyperbolic) :
    Fibration.Equivalent h f ∨ Fibration.Equivalent h g := by
  obtain ⟨hfinite, hsurj⟩ := K.finite_pair f g hf hg hne
  exact RamificationSupport.third_equivalent_of_empty_ramification K.unramifiedSurfaceCovering
    K.productRigidity K.productCovers K.fibreConstancy K.localSections
    (FibreGeometry.compactCurveMapTheorem K.curveMaps) K.inverseCurveMap f g hB hC
    hfinite hsurj hempty h hH

end ClassicalInputs
end Paper27.Geometry
