import Paper27
noncomputable section
open scoped Manifold Topology BigOperators
open Paper27.Geometry
namespace P27PaperCheck

theorem at_most_two :
  ∀ (K : ClassicalInputs) (X : CompactComplexSurface), AtMostTwoSmoothHyperbolicFibrations X :=
  by sorry

theorem at_most_two_classes :
  ∀ (K : ClassicalInputs) (X : CompactComplexSurface), AtMostTwoFibrationClasses X :=
  by sorry

theorem kodaira :
  ∀ (K : ClassicalInputs), KodairaBaseHyperbolicity →
  ∀ X : CompactComplexSurface, AtMostTwoKodairaFibrations X :=
  by sorry

theorem finite_pair :
  ∀ (K : ClassicalInputs) {X : CompactComplexSurface} (f g : Fibration X),
  f.Smooth → g.Smooth → ¬ Fibration.Equivalent f g → f.FinitePair g ∧ f.PairSurjective g :=
  by sorry

theorem connection_degree_zero :
  ∀ (K : ClassicalInputs) (D : Curve) (L : HolomorphicLineCocycle D),
  Nonempty L.Connection → K.degreeTheory.degree D L = 0 :=
  by sorry

theorem bott_degree_zero :
  ∀ (K : ClassicalInputs) (X : CompactComplexSurface) (D : EmbeddedCurve X)
  (U : D.Neighbourhood) (r : D.Retraction U) (N T : HolomorphicLineCocycle D.curve)
  (F : EmbeddedFrames.RawEmbeddedFrames D N T)
  (L : NeighbourhoodSplittings.HolomorphicLineSubbundle r),
  (∀ p : D.curve, L.lineAt (NeighbourhoodSplittings.curvePoint U p) =
    LinearMap.range (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ) D.inclusion p).toLinearMap) →
  K.degreeTheory.degree D.curve N = 0 :=
  by sorry

theorem curve_metric_rigidity :
  ∀ (K : CurveBranchInputs) {D B C : Curve} (u : HolomorphicMap D B) (v : HolomorphicMap D C)
  (hu : MetricComparison.Nonconstant u) (hv : MetricComparison.Nonconstant v),
  B.Hyperbolic → C.Hyperbolic →
  MetricComparison.ramificationDivisor u (K.curveMaps.ramification_finite D B u hu) =
    MetricComparison.ramificationDivisor v (K.curveMaps.ramification_finite D C v hv) →
  MetricComparison.pullback u (K.metrics.metric B) = MetricComparison.pullback v (K.metrics.metric C) ∧
  ∀ p : D, Nonempty (LocalIsometryGraph u v (K.metrics.metric B) (K.metrics.metric C) p) :=
  by sorry

theorem ramification_geometry :
  ∀ (K : ClassicalInputs) {X : CompactComplexSurface} (f g : Fibration X),
  f.Smooth → g.Smooth → f.Hyperbolic → g.Hyperbolic → ¬ Fibration.Equivalent f g →
  ∃ (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g) (F : RamificationCurveFamily f g),
    ∀ i, Nonempty (RamificationComponentGeometry K f g hfinite hsurj (F.member i)) :=
  by sorry

theorem checking_both_projections :
  ∀ (maps : MetricComparison.ClassicalCurveMapFacts),
  CheckingBothProjections.ZaalIntermediateConstruction →
  ∃ (X : CompactComplexSurface) (B : Curve) (h : HolomorphicMap X B),
    ¬ CheckingBothProjections.IsSubmersion h :=
  by sorry

theorem common_component_indices :
  ∀ (K : ClassicalInputs) {X : CompactComplexSurface} (f g h : Fibration X),
  f.Smooth → g.Smooth → h.Smooth → f.Hyperbolic → g.Hyperbolic → h.Hyperbolic →
  ∀ (hfinite12 : f.FinitePair g) (hsurj12 : f.PairSurjective g)
    (hfinite13 : f.FinitePair h) (hsurj13 : f.PairSurjective h)
    (hfinite23 : g.FinitePair h) (hsurj23 : g.PairSurjective h)
    (D : EmbeddedCurve X), D.curve.Hyperbolic → D.TangentToPair f g →
    D.TangentToPair f h → D.TangentToPair g h →
    Nonempty (CommonComponentIndices f g h hfinite12 hsurj12 hfinite13 hsurj13
      hfinite23 hsurj23 D) :=
  by sorry

theorem component_alternatives :
  ∀ (K : ClassicalInputs), HolomorphicEmbeddedFactorization →
  ∀ {X : CompactComplexSurface} (f g h : Fibration X),
  f.Smooth → g.Smooth → h.Smooth → f.Hyperbolic → g.Hyperbolic → h.Hyperbolic →
  ¬ Fibration.Equivalent f g → ¬ Fibration.Equivalent f h → ¬ Fibration.Equivalent g h →
  ∃ (hfinite12 : f.FinitePair g) (hsurj12 : f.PairSurjective g)
    (hfinite13 : f.FinitePair h) (hsurj13 : f.PairSurjective h)
    (hfinite23 : g.FinitePair h) (hsurj23 : g.PairSurjective h)
    (F12 : RamificationCurveFamily f g) (F13 : RamificationCurveFamily f h)
    (F23 : RamificationCurveFamily g h), ∀ i : F12.Index,
    let D := F12.member i
    (D.DisjointFromPair f h ∧ D.DisjointFromPair g h) ∨
    (D.TangentToPair f h ∧ D.TangentToPair g h ∧
      (∃ i j, D.support = (F13.member i).support ∧ D.support = (F23.member j).support) ∧
      Nonempty (CommonComponentIndices f g h hfinite12 hsurj12 hfinite13 hsurj13
        hfinite23 hsurj23 D)) :=
  by sorry

theorem actual_divisor_coefficient :
  ∀ {X Y : CompactComplexSurface}
  {q : RamificationSupport.FiniteSurjectiveHolomorphicMap X Y} {p : X}
  (A : RamificationIndexConstancy.SurfaceCyclicChart q p) {x : X},
  x ∈ A.source.source → x ∈ RamificationIndexConstancy.criticalSet q →
    RamificationDivisorOrder.divisorCoefficient A x = A.exponent - 1 :=
  by sorry

theorem disjoint_impossible :
  ∀ (K : ClassicalInputs) {X : CompactComplexSurface} {D : EmbeddedCurve X}
  {U : D.Neighbourhood} {r s : D.Retraction U} {n : ℕ}
  (A : RetractionCoordinateGerms.NormalAtlas D U r s n), 2 ≤ n →
  ∀ f h : Fibration X, RetractionFactorization.Factorization r f → D.Unramified f →
    D.DisjointFromPair f h → D.curve.Hyperbolic → False :=
  by sorry

theorem original_common_obstruction :
  ∀ (K : ClassicalInputs) (Q : AveragingInputs) {X : CompactComplexSurface} (f g h : Fibration X),
  f.Smooth → g.Smooth → h.Smooth → f.Hyperbolic → g.Hyperbolic → h.Hyperbolic →
  ¬ Fibration.Equivalent f g → ¬ Fibration.Equivalent f h → ¬ Fibration.Equivalent g h →
  ∀ D : EmbeddedCurve X, D.curve.Hyperbolic → D.TangentToPair f g →
    D.TangentToPair f h → D.TangentToPair g h → False :=
  by sorry

theorem appendix_common_obstruction :
  ∀ (K : ClassicalInputs) {X : CompactComplexSurface} {D : EmbeddedCurve X}
  {U : D.Neighbourhood} {r s t : D.Retraction U} {n m k : ℕ},
  RetractionCoordinateGerms.NormalAtlas D U r s n →
  RetractionCoordinateGerms.NormalAtlas D U r t m →
  RetractionCoordinateGerms.NormalAtlas D U s t k →
  2 ≤ n → 2 ≤ m → 2 ≤ k → D.curve.Hyperbolic → False :=
  by sorry

theorem unramified_pair :
  ∀ (K : ClassicalInputs) {X : CompactComplexSurface} {C D : Curve}, C.Hyperbolic → D.Hyperbolic →
  ∀ (q : FiniteUnramifiedCover X (C.productSurface D))
    (hc : ∀ c : C, IsConnected ((fun x : X => (q.map x).1) ⁻¹' {c}))
    (hd : ∀ d : D, IsConnected ((fun x : X => (q.map x).2) ⁻¹' {d}))
    (h : Fibration X), h.Hyperbolic →
    Fibration.Equivalent h (q.firstFibration hc) ∨ Fibration.Equivalent h (q.secondFibration hd) :=
  by sorry

theorem product_exactly_two :
  ∀ (K : ClassicalInputs) (C D : Curve), C.Hyperbolic → D.Hyperbolic →
  ExactlyTwoSmoothHyperbolicFibrationClasses (C.productSurface D) :=
  by sorry

theorem double_kodaira_attains_bound :
  ∀ (K : ClassicalInputs), KodairaBaseHyperbolicity → DoubleKodairaExistence →
  ∃ X : CompactComplexSurface, ExactlyTwoSmoothHyperbolicFibrationClasses X ∧
    ExactlyTwoKodairaFibrationClasses X :=
  by sorry


end P27PaperCheck
