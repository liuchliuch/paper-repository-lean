import Paper27.Geometry.ActualCyclicModels
import Paper27.Geometry.UniformCyclicRestrictions

/-!
# Explicit universal classical inputs for constructing the curve geometry

Every field below is a general classical theorem, quantified over arbitrary
actual maps or metrics. In particular this package contains no ramification
curve family, local model for a pair of fibrations, retraction atlas, normal
degree assertion, third-fibration conclusion, or fibration bound.

The methods construct actual models and actual unramified restrictions from
these inputs by the previously proved normalization, metric, and branch
arguments. This package is only a readable grouping of explicit parameters.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry
open MetricComparison NormalizedBranchConstruction FixedAmbientBranchGraphs

structure CurveBranchInputs where
  regularity : CoordinateCalculus.SurfaceAnalyticRegularity
  curveMaps : ClassicalCurveMapFacts
  zeroDifferential : CovectorGauges.ClassicalZeroDifferentialConstancy
  pullbacks : ClassicalPullbackFacts
  negativeCurvatureUniqueness : TroyanovUniqueness
  discExtension : DiscGraphExtension.LocalDiscIsometryExtension
  finiteRepresentatives : CoordinateFiniteGerms.FiniteHolomorphicGermRepresentatives
  isometryRigidity : BranchGraphs.IsometryFirstJetRigidity
  finiteCoverClassification : FiniteAnalyticGerm.SmoothBranchFiniteCoverClassification
  metrics : MetricTangency.HyperbolicMetricTheory
  uniformizingCharts : UniformizingDiscCharts
  normalization : CriticalCurveNormalizationTheorem

namespace CurveBranchInputs
variable {X : CompactComplexSurface} (K : CurveBranchInputs)

/-- Construct an actual Euclidean cyclic model at each actual critical point,
in actual uniformizing target coordinates chosen from the actual metrics. -/
theorem euclidean_model_exists (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (x : X) (hx : x ∈ RamificationSupport.ramificationSet f g) :
    ∃ (a : UniformizingDiscChart (K.metrics.metric f.base) (f x))
      (d : UniformizingDiscChart (K.metrics.metric g.base) (g x))
      (B : CyclicModel.CyclicNormalForm
        (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
        (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
        ((chartAt (ℂ × ℂ) x) x)),
      2 ≤ B.exponent ∧ ∀ z ∈ B.coordinate.chart.source,
        Valid a (CoordinateCalculus.fibrationMap f) x z ∧
          Valid d (CoordinateCalculus.fibrationMap g) x z := by
  obtain ⟨a⟩ := K.uniformizingCharts f.base (K.metrics.metric f.base) hB
    (K.metrics.cone f.base hB) (K.metrics.curvature f.base hB) (f x)
  obtain ⟨d⟩ := K.uniformizingCharts g.base (K.metrics.metric g.base) hC
    (K.metrics.cone g.base hC) (K.metrics.curvature g.base hC) (g x)
  obtain ⟨B, hn, hvalid⟩ := ActualCyclicModels.cyclic_model_exists K.regularity K.curveMaps
    K.zeroDifferential K.pullbacks K.negativeCurvatureUniqueness K.discExtension
    K.finiteRepresentatives K.isometryRigidity K.finiteCoverClassification hf hg hB
    hfinite hsurj N (K.metrics.cone f.base hB) (K.metrics.cone g.base hC)
    (K.metrics.curvature f.base hB) (K.metrics.curvature g.base hC) x hx a d
  exact ⟨a, d, B, hn, hvalid⟩

include K
/-- Any actual embedded curve in the paired critical set has both actual
unramified projection restrictions. This now starts with the original maps;
no cyclic-atlas or unramified-restriction data is a premise. -/
theorem unramified_of_tangency (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (D : EmbeddedCurve X) (hD : D.TangentToPair f g) : D.Unramified f ∧ D.Unramified g := by
  have hpoint : ∀ p : D.curve,
      Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p) ∧
        Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap g) p) := by
    intro p
    obtain ⟨a, d, B, _hn, _hvalid⟩ := K.euclidean_model_exists f g hf hg hB hC
      hfinite hsurj N (D.inclusion p) (hD ⟨p, rfl⟩)
    exact UniformCyclicRestrictions.restrictions_bijective D hD p a d B (hg _)
  exact ⟨fun p => (hpoint p).1, fun p => (hpoint p).2⟩

end CurveBranchInputs
end Paper27.Geometry
