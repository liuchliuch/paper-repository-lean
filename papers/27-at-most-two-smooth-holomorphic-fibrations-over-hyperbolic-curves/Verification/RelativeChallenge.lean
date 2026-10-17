import Paper27
noncomputable section
open scoped BigOperators Manifold
open Polynomial
open Paper27.Geometry
namespace P27RelativeCheck

theorem product_two :
    ∀ (C D : Curve), C.Hyperbolic → D.Hyperbolic →
    ∃ f g : HyperbolicSmoothFibration (C.productSurface D),
      ¬ Fibration.Equivalent f.val g.val :=
  by sorry

theorem finite_pair :
    ∀ (curveMaps : NonconstantCompactCurveMapTheorem)
    (inverseTheorem : BijectiveHolomorphicInverse)
    {X : CompactComplexSurface} (f g : Fibration X),
    f.Smooth → g.Smooth →
    (f.Smooth → ∀ b, FibreCurveModel f b) →
    (f.Smooth → Fibration.FibreDegreeFacts f g) →
    (f.Smooth → Fibration.LocalHolomorphicSections f) →
    ¬ Fibration.Equivalent f g → f.FinitePair g ∧ f.PairSurjective g :=
  by sorry

theorem unramified_pair :
    ∀ (rigidity : ProductCurveRigidity)
    (productCovers : ProductCoverExistence)
    (constancy : ConnectedFibreDerivativeConstancy)
    (sections : HolomorphicSubmersionSections)
    (curveMaps : NonconstantCompactCurveMapTheorem)
    (inverseTheorem : BijectiveHolomorphicInverse)
    {X : CompactComplexSurface} {C D : Curve}, C.Hyperbolic → D.Hyperbolic →
    ∀ (q : FiniteUnramifiedCover X (C.productSurface D))
    (hc : ∀ c : C, IsConnected ((fun x : X => (q.map x).1) ⁻¹' {c}))
    (hd : ∀ d : D, IsConnected ((fun x : X => (q.map x).2) ⁻¹' {d}))
    (h : Fibration X), h.Hyperbolic →
    Fibration.Equivalent h (q.firstFibration hc) ∨
      Fibration.Equivalent h (q.secondFibration hd) :=
  by sorry

theorem empty_ramification :
    ∀ {X : CompactComplexSurface}
    (coveringTheorem : RamificationSupport.ProperHolomorphicLocalDiffeomorphismCovering)
    (rigidity : ProductCurveRigidity) (productCovers : ProductCoverExistence)
    (constancy : ConnectedFibreDerivativeConstancy) (sections : HolomorphicSubmersionSections)
    (curveMaps : NonconstantCompactCurveMapTheorem) (inverseTheorem : BijectiveHolomorphicInverse)
    (f g : Fibration X), f.Hyperbolic → g.Hyperbolic →
    f.FinitePair g → f.PairSurjective g → RamificationSupport.ramificationSet f g = ∅ →
    ∀ h : Fibration X, h.Hyperbolic → Fibration.Equivalent h f ∨ Fibration.Equivalent h g :=
  by sorry

theorem equal_pullback_metrics :
    ∀ (maps : MetricComparison.ClassicalCurveMapFacts)
    (pullbacks : MetricComparison.ClassicalPullbackFacts) (unique : MetricComparison.TroyanovUniqueness)
    {D B C : Curve} (u : HolomorphicMap D B) (v : HolomorphicMap D C),
    MetricComparison.Nonconstant u → MetricComparison.Nonconstant v → B.Hyperbolic →
    ∀ (gB : MetricComparison.ConformalMetric B) (gC : MetricComparison.ConformalMetric C),
    MetricComparison.HasConeData gB 0 → MetricComparison.HasConeData gC 0 →
    MetricComparison.HasConstantCurvature gB 0 (-1) →
    MetricComparison.HasConstantCurvature gC 0 (-1) →
    (∀ p, MetricComparison.ramificationOrder u p = MetricComparison.ramificationOrder v p) →
    MetricComparison.pullback u gB = MetricComparison.pullback v gC :=
  by sorry

theorem appendix_connection_obstruction :
    ∀ (theory : LineBundleDegreeTheory)
    (D : Curve) (T : TangentLineCocycle D), D.Hyperbolic →
    ∀ (n : ℕ), 2 ≤ n → ∀ (a : ℂ), a ≠ 0 → a ≠ 1 →
    ∀ (b : D → D → ℂ),
    (∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b i) (D.chartDomain i)) →
    CompatibleRetractionJets D T n a b → False :=
  by sorry

theorem product_bound :
    ∀ (rigidity : ProductCurveRigidity)
    (curveMaps : NonconstantCompactCurveMapTheorem) (inverseTheorem : BijectiveHolomorphicInverse)
    (C D : Curve), AtMostTwoSmoothHyperbolicFibrations (C.productSurface D) :=
  by sorry

theorem disc_graph_extension :
    ∀ (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    {u v : ℂ → ℂ} {U : Set ℂ}, IsOpen U → IsPreconnected U →
    AnalyticOnNhd ℂ u U → AnalyticOnNhd ℂ v U →
    (∀ z ∈ U, ‖u z‖ < 1) → (∀ z ∈ U, ‖v z‖ < 1) →
    (∀ z ∈ U, BranchGraphs.poincareDensity (u z) * ‖deriv u z‖ ^ 2 =
      BranchGraphs.poincareDensity (v z) * ‖deriv v z‖ ^ 2) →
    ∀ regular : ℂ, regular ∈ U → deriv u regular ≠ 0 →
    ∃ A : DiscGraphExtension.GlobalDiscIsometry, ∀ z ∈ U, v z = A (u z) :=
  by sorry

end P27RelativeCheck
