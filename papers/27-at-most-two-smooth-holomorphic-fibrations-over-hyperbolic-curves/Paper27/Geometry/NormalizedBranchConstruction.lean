import Paper27.Geometry.CoordinateCalculus
import Paper27.Geometry.DiscGraphExtension

/-!
# Constructing normalized branch graphs from equal metrics

The graph and its slope are conclusions here. For actual analytic coordinate
functions and a normalization map, equality of their Poincaré pullback
densities gives a global disc isometry on a connected source neighbourhood.
Finite analytic order of the first coordinate derivative supplies regular
points accumulating at the normalization centre, including when that centre
is ramified. The resulting data form an actual `NormalizedBranchGraph`.

The metric coordinate bridge below uses actual manifold differentials and
the defined pullback quadratic form. Uniformizing coordinates are stated as
a separate universal classical input for actual hyperbolic curve metrics;
their specification does not mention normalizations or branch graphs.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.NormalizedBranchConstruction

open BranchGraphs MetricComparison

/-- Finite order rules out local vanishing of the actual derivative, hence
gives regular points accumulating at the centre in any open neighbourhood. -/
theorem centre_mem_closure_regular {u : ℂ → ℂ} {U : Set ℂ} {c : ℂ}
    (hU : IsOpen U) (hc : c ∈ U)
    (hfinite : analyticOrderAt (deriv u) c ≠ ⊤) :
    c ∈ closure {z | z ∈ U ∧ deriv u z ≠ 0} := by
  have hnonzero : ∃ᶠ z in 𝓝 c, deriv u z ≠ 0 := by
    change ¬ (∀ᶠ z in 𝓝 c, ¬ deriv u z ≠ 0)
    intro hzero
    apply hfinite
    apply analyticOrderAt_eq_top.mpr
    simpa only [not_not] using hzero
  exact mem_closure_iff_frequently.mpr
    ((hnonzero.and_eventually (hU.mem_nhds hc)).mono fun _ h => ⟨h.2, h.1⟩)

/-- Actual local normalization and metric data. Neither a graph function nor
a proportionality scalar is a field. Finite derivative order is the usual
nonconstant analytic curve-map condition, expressed for the actual function. -/
structure MetricBranchData (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) where
  normalization : ℂ → ℂ × ℂ
  centre : ℂ
  centre_maps : normalization centre = p
  domain : Set ℂ
  open_domain : IsOpen domain
  connected_domain : IsPreconnected domain
  centre_mem : centre ∈ domain
  normalization_analytic : AnalyticOnNhd ℂ normalization domain
  first_analytic : ∀ z ∈ domain, AnalyticAt ℂ F (normalization z)
  second_analytic : ∀ z ∈ domain, AnalyticAt ℂ G (normalization z)
  first_surjective : ∀ z ∈ domain, Function.Surjective (fderiv ℂ F (normalization z))
  second_surjective : ∀ z ∈ domain, Function.Surjective (fderiv ℂ G (normalization z))
  joint_not_surjective : ∀ z ∈ domain, ¬ Function.Surjective
    (fun v : ℂ × ℂ => (fderiv ℂ F (normalization z) v,
      fderiv ℂ G (normalization z) v))
  first_disc : ∀ z ∈ domain, ‖F (normalization z)‖ < 1
  second_disc : ∀ z ∈ domain, ‖G (normalization z)‖ < 1
  metric_identity : ∀ z ∈ domain,
    poincareDensity (F (normalization z)) * ‖deriv (F ∘ normalization) z‖ ^ 2 =
      poincareDensity (G (normalization z)) * ‖deriv (G ∘ normalization) z‖ ^ 2
  derivative_order_finite : analyticOrderAt (deriv (F ∘ normalization)) centre ≠ ⊤

namespace MetricBranchData

variable {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ}

def regular (A : MetricBranchData F G p) : Set ℂ :=
  {z | z ∈ A.domain ∧ deriv (F ∘ A.normalization) z ≠ 0}

theorem centre_in_closure (A : MetricBranchData F G p) :
    A.centre ∈ closure A.regular :=
  centre_mem_closure_regular A.open_domain A.centre_mem A.derivative_order_finite

theorem regular_nonempty (A : MetricBranchData F G p) : A.regular.Nonempty := by
  exact (Set.nonempty_of_mem A.centre_in_closure).of_closure

theorem first_composite_analytic (A : MetricBranchData F G p) :
    AnalyticOnNhd ℂ (F ∘ A.normalization) A.domain :=
  fun z hz => (A.first_analytic z hz).comp (A.normalization_analytic z hz)

theorem second_composite_analytic (A : MetricBranchData F G p) :
    AnalyticOnNhd ℂ (G ∘ A.normalization) A.domain :=
  fun z hz => (A.second_analytic z hz).comp (A.normalization_analytic z hz)

/-- The only extension input is the universal local disc isometry theorem.
The actual regular inverse and graph identity are constructed by the already
proved `graph_across_ramification`. -/
theorem global_graph_exists (A : MetricBranchData F G p)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension) :
    ∃ graph : DiscGraphExtension.GlobalDiscIsometry,
      ∀ z ∈ A.domain, G (A.normalization z) = graph (F (A.normalization z)) := by
  obtain ⟨r, hr⟩ := A.regular_nonempty
  exact DiscGraphExtension.graph_across_ramification extend A.open_domain A.connected_domain
    A.first_composite_analytic A.second_composite_analytic A.first_disc A.second_disc
    A.metric_identity r hr.1 hr.2

/-- Restriction of an actual global Poincaré isometry to its actual unit-disc
domain gives precisely the local-isometry data required by branch rigidity. -/
def localGraph (A : MetricBranchData F G p) (graph : DiscGraphExtension.GlobalDiscIsometry) :
    LocalDiscIsometry (F p) where
  toFun := graph.toFun
  domain := Metric.ball 0 1
  open_domain := Metric.isOpen_ball
  centre_mem := by
    have h := A.first_disc A.centre A.centre_mem
    simpa only [A.centre_maps, Metric.mem_ball, dist_zero_right] using h
  domain_disc z hz := by simpa only [Metric.mem_ball, dist_zero_right] using hz
  maps_disc z hz := graph.maps_disc z (by simpa only [Metric.mem_ball, dist_zero_right] using hz)
  analytic := graph.analytic
  metric_identity z hz := graph.metric_identity z
    (by simpa only [Metric.mem_ball, dist_zero_right] using hz)

/-- Equality of the actual pulled-back densities produces the actual
normalized branch graph. The derivative relation at regular points is the
chain rule; density of those points follows from finite analytic order. -/
def normalizedBranchGraph (A : MetricBranchData F G p)
    (graph : DiscGraphExtension.GlobalDiscIsometry)
    (hgraph : ∀ z ∈ A.domain,
      G (A.normalization z) = graph (F (A.normalization z))) :
    NormalizedBranchGraph F G p where
  normalization := A.normalization
  centre := A.centre
  centre_maps := A.centre_maps
  normalization_analytic := A.normalization_analytic A.centre A.centre_mem
  regular := A.regular
  centre_in_closure := A.centre_in_closure
  first_differentiable z hz := (A.first_analytic z hz.1).differentiableAt
  second_differentiable z hz := (A.second_analytic z hz.1).differentiableAt
  normalization_differentiable z hz := (A.normalization_analytic z hz.1).differentiableAt
  first_surjective z hz := A.first_surjective z hz.1
  second_surjective z hz := A.second_surjective z hz.1
  joint_not_surjective z hz := A.joint_not_surjective z hz.1
  regular_first_derivative z hz := by
    have hchain := (A.first_analytic z hz.1).differentiableAt.hasFDerivAt.comp_hasDerivAt z
      (A.normalization_analytic z hz.1).differentiableAt.hasDerivAt
    rw [← hchain.deriv]
    exact hz.2
  graph := A.localGraph graph
  regular_image z hz := by
    simpa only [localGraph, Metric.mem_ball, dist_zero_right] using A.first_disc z hz.1
  graph_identity z hz := by
    exact Filter.eventually_of_mem (A.open_domain.mem_nhds hz.1) fun t ht => hgraph t ht

theorem normalizedBranchGraph_exists (A : MetricBranchData F G p)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension) :
    Nonempty (NormalizedBranchGraph F G p) := by
  obtain ⟨graph, hgraph⟩ := A.global_graph_exists extend
  exact ⟨A.normalizedBranchGraph graph hgraph⟩

end MetricBranchData

/-- The explicit model coordinate on a tangent space of the scalar model.
As for `MetricComparison.tangentCoordinate`, this avoids imposing an
intrinsic norm on a manifold tangent-space type. -/
def discTangentCoordinate (z : ℂ) (v : TangentSpace 𝓘(ℂ, ℂ) z) : ℂ := v

/-- A genuine uniformizing coordinate of an actual curve metric. The law is
an equality of the actual quadratic forms under the actual chart derivative.
No normalization, branch graph, or differential proportionality is specified. -/
structure UniformizingDiscChart {B : Curve} (g : ConformalMetric B) (b : B) where
  coordinates : OpenPartialHomeomorph B ℂ
  centre_mem : b ∈ coordinates.source
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) coordinates coordinates.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
    coordinates.symm coordinates.target
  target_disc : ∀ z ∈ coordinates.target, ‖z‖ < 1
  metric_identity : ∀ q ∈ coordinates.source,
    ∀ w : TangentSpace 𝓘(ℂ, ℂ) q,
      squaredNorm g q w = poincareDensity (coordinates q) *
        ‖discTangentCoordinate (coordinates q)
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) coordinates q w)‖ ^ 2

/-- Classical local uniformization of an actual smooth curvature-minus-one
metric on an actual hyperbolic compact curve. Its conclusion is just a chart
and the actual metric coordinate law specified above. -/
def UniformizingDiscCharts : Prop :=
  ∀ (B : Curve) (g : ConformalMetric B), B.Hyperbolic → HasConeData g 0 →
    HasConstantCurvature g 0 (-1) → ∀ b : B, Nonempty (UniformizingDiscChart g b)

namespace UniformizingDiscChart

variable {D B C : Curve} {gB : ConformalMetric B} {gC : ConformalMetric C}
  {b : B} {c : C}

def mdifferentiable (a : UniformizingDiscChart gB b) :
    a.coordinates.MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) :=
  ⟨a.holomorphic, a.inverse_holomorphic⟩

/-- The actual expression of a curve map in its canonical source chart and
the actual uniformizing target chart. -/
def coordinateFunction (a : UniformizingDiscChart gB b) (u : HolomorphicMap D B)
    (p : D) : ℂ → ℂ := a.coordinates ∘ u ∘ (chartAt ℂ p).symm

theorem coordinateFunction_deriv (a : UniformizingDiscChart gB b)
    (u : HolomorphicMap D B) (p : D) {z : ℂ}
    (hz : z ∈ (chartAt ℂ p).target)
    (ha : u ((chartAt ℂ p).symm z) ∈ a.coordinates.source) :
    deriv (a.coordinateFunction u p) z =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a.coordinates (u ((chartAt ℂ p).symm z))
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u ((chartAt ℂ p).symm z)
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm z (1 : ℂ))) := by
  have hi := (mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) p).mdifferentiableAt_symm hz
  have hau := a.holomorphic.mdifferentiableAt (a.coordinates.open_source.mem_nhds ha)
  rw [← fderiv_deriv, ← mfderiv_eq_fderiv]
  unfold coordinateFunction
  rw [mfderiv_comp z hau ((u.holomorphic _).comp z hi),
    mfderiv_comp z (u.holomorphic _) hi]
  rfl

theorem coordinateFunction_disc (a : UniformizingDiscChart gB b)
    (u : HolomorphicMap D B) (p : D) {z : ℂ}
    (ha : u ((chartAt ℂ p).symm z) ∈ a.coordinates.source) :
    ‖a.coordinateFunction u p z‖ < 1 :=
  a.target_disc _ (a.coordinates.map_source ha)

theorem eventually_domains (a : UniformizingDiscChart gB b)
    (u : HolomorphicMap D B) (p : D) (hp : u p ∈ a.coordinates.source) :
    ∀ᶠ z in 𝓝 ((chartAt ℂ p) p), z ∈ (chartAt ℂ p).target ∧
      u ((chartAt ℂ p).symm z) ∈ a.coordinates.source := by
  have hi := (chartAt ℂ p).continuousAt_symm
    ((chartAt ℂ p).map_source (mem_chart_source ℂ p))
  have hu := u.holomorphic.continuous.continuousAt.comp hi
  have hcentre : (u ∘ (chartAt ℂ p).symm) ((chartAt ℂ p) p) = u p := by
    simp only [Function.comp_apply, (chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
  have ht := hu.tendsto (a.coordinates.open_source.mem_nhds (hcentre.symm ▸ hp))
  filter_upwards [ht, (chartAt ℂ p).open_target.mem_nhds
    ((chartAt ℂ p).map_source (mem_chart_source ℂ p))] with z hz hzt
  exact ⟨hzt, hz⟩

theorem coordinateFunction_analytic (a : UniformizingDiscChart gB b)
    (u : HolomorphicMap D B) (p : D) (hp : u p ∈ a.coordinates.source) :
    AnalyticAt ℂ (a.coordinateFunction u p) ((chartAt ℂ p) p) := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [a.eventually_domains u p hp] with z hz
  apply mdifferentiableAt_iff_differentiableAt.mp
  exact (a.mdifferentiable.mdifferentiableAt hz.2).comp z
    ((u.holomorphic _).comp z
      ((mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) p).mdifferentiableAt_symm hz.1))

/-- A change to a genuine uniformizing target chart preserves the zero set
of the actual curve-coordinate derivative. -/
theorem coordinateFunction_deriv_eq_zero_iff (a : UniformizingDiscChart gB b)
    (u : HolomorphicMap D B) (p : D) {z : ℂ}
    (hz : z ∈ (chartAt ℂ p).target)
    (ha : u ((chartAt ℂ p).symm z) ∈ a.coordinates.source)
    (hb : u ((chartAt ℂ p).symm z) ∈ (chartAt ℂ (u p)).source) :
    deriv (a.coordinateFunction u p) z = 0 ↔
      deriv (writtenCoordinateMap u p) z = 0 := by
  have hstandard : deriv (writtenCoordinateMap u p) z =
      mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ (u p)) (u ((chartAt ℂ p).symm z))
        (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u ((chartAt ℂ p).symm z)
          (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm z (1 : ℂ))) := by
    rw [← fderiv_deriv]
    change fderiv ℂ (CoordinateCalculus.coordinateMap u p (u p)) z (1 : ℂ) = _
    rw [CoordinateCalculus.coordinateMap_derivative u p (u p) hz hb]
    rfl
  rw [a.coordinateFunction_deriv u p hz ha, hstandard]
  exact ⟨fun h => by
    have hv := (a.mdifferentiable.mfderiv_injective ha)
      (h.trans (map_zero _).symm)
    rw [hv, map_zero], fun h => by
    have hv := ((mdifferentiable_chart (I := 𝓘(ℂ, ℂ)) (u p)).mfderiv_injective hb)
      (h.trans (map_zero _).symm)
    rw [hv, map_zero]⟩

/-- Finiteness of derivative order for the actual nonconstant curve map is
transported to the actual uniformizing coordinate, rather than assumed of
the new coordinate function. -/
theorem coordinateFunction_derivative_order_finite (a : UniformizingDiscChart gB b)
    (maps : ClassicalCurveMapFacts) (u : HolomorphicMap D B) (hu : Nonconstant u)
    (p : D) (hp : u p ∈ a.coordinates.source) :
    analyticOrderAt (deriv (a.coordinateFunction u p)) ((chartAt ℂ p) p) ≠ ⊤ := by
  intro htop
  apply maps.derivative_order_finite D B u hu p
  apply analyticOrderAt_eq_top.mpr
  filter_upwards [analyticOrderAt_eq_top.mp htop,
    a.eventually_domains u p hp, CoordinateCalculus.coordinateMap_eventually_domains u p]
    with z hz ha hb
  exact (a.coordinateFunction_deriv_eq_zero_iff u p ha.1 ha.2 hb.2).mp hz

/-- Equality of the actual pullback metrics implies equality of the actual
Poincaré pullback densities in any valid pair of uniformizing coordinates.
The proof is the pullback quadratic-form identity followed by the chain rule. -/
theorem pullback_density_eq (a : UniformizingDiscChart gB b)
    (d : UniformizingDiscChart gC c)
    (u : HolomorphicMap D B) (v : HolomorphicMap D C) (p : D)
    (hmetric : pullback u gB = pullback v gC) {z : ℂ}
    (hz : z ∈ (chartAt ℂ p).target)
    (ha : u ((chartAt ℂ p).symm z) ∈ a.coordinates.source)
    (hd : v ((chartAt ℂ p).symm z) ∈ d.coordinates.source) :
    poincareDensity (a.coordinateFunction u p z) *
        ‖deriv (a.coordinateFunction u p) z‖ ^ 2 =
      poincareDensity (d.coordinateFunction v p z) *
        ‖deriv (d.coordinateFunction v p) z‖ ^ 2 := by
  let q := (chartAt ℂ p).symm z
  let w : TangentSpace 𝓘(ℂ, ℂ) q :=
    mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm z (1 : ℂ)
  have heq := congrArg (fun k : ConformalMetric D => squaredNorm k q w) hmetric
  change squaredNorm (pullback u gB) q w = squaredNorm (pullback v gC) q w at heq
  rw [pullback_squaredNorm, pullback_squaredNorm] at heq
  rw [a.metric_identity _ ha, d.metric_identity _ hd] at heq
  rw [a.coordinateFunction_deriv u p hz ha, d.coordinateFunction_deriv v p hz hd]
  exact heq

/-- For actual nonconstant holomorphic curve maps with equal actual pullback
metrics, a graph across the ramification centre is constructed in actual
uniformizing coordinates. The regular point and its inverse chart are
conclusions, as is the graph itself. -/
theorem local_graph_of_equal_pullbacks (a : UniformizingDiscChart gB b)
    (d : UniformizingDiscChart gC c) (maps : ClassicalCurveMapFacts)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (u : HolomorphicMap D B) (v : HolomorphicMap D C) (hu : Nonconstant u) (p : D)
    (hp : u p ∈ a.coordinates.source) (hq : v p ∈ d.coordinates.source)
    (hmetric : pullback u gB = pullback v gC) :
    ∃ U : Set ℂ, IsOpen U ∧ IsPreconnected U ∧ (chartAt ℂ p) p ∈ U ∧
      ∃ graph : DiscGraphExtension.GlobalDiscIsometry,
        ∀ z ∈ U, d.coordinateFunction v p z = graph (a.coordinateFunction u p z) := by
  let x := (chartAt ℂ p) p
  have hau := a.coordinateFunction_analytic u p hp
  have hdv := d.coordinateFunction_analytic v p hq
  have hnear : {z | z ∈ (chartAt ℂ p).target ∧
      u ((chartAt ℂ p).symm z) ∈ a.coordinates.source ∧
      v ((chartAt ℂ p).symm z) ∈ d.coordinates.source ∧
      AnalyticAt ℂ (a.coordinateFunction u p) z ∧
      AnalyticAt ℂ (d.coordinateFunction v p) z} ∈ 𝓝 x := by
    filter_upwards [a.eventually_domains u p hp, d.eventually_domains v p hq,
      hau.eventually_analyticAt, hdv.eventually_analyticAt] with z ha hd haza hdza
    exact ⟨ha.1, ha.2, hd.2, haza, hdza⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let U := Metric.ball x r
  have hx : x ∈ U := by exact Metric.mem_ball_self hr
  have hcl : x ∈ closure {z | z ∈ U ∧ deriv (a.coordinateFunction u p) z ≠ 0} :=
    centre_mem_closure_regular Metric.isOpen_ball hx
      (a.coordinateFunction_derivative_order_finite maps u hu p hp)
  obtain ⟨regular, hregular⟩ := (Set.nonempty_of_mem hcl).of_closure
  obtain ⟨graph, hgraph⟩ := DiscGraphExtension.graph_across_ramification extend
    (U := U) Metric.isOpen_ball (convex_ball x r).isPreconnected
    (fun z hz => (hball hz).2.2.2.1) (fun z hz => (hball hz).2.2.2.2)
    (fun z hz => a.coordinateFunction_disc u p (hball hz).2.1)
    (fun z hz => d.coordinateFunction_disc v p (hball hz).2.2.1)
    (fun z hz => a.pullback_density_eq d u v p hmetric (hball hz).1
      (hball hz).2.1 (hball hz).2.2.1)
    regular hregular.1 hregular.2
  exact ⟨U, Metric.isOpen_ball, (convex_ball x r).isPreconnected, hx, graph, hgraph⟩

end UniformizingDiscChart

/-- The global normalization comparison feeds the local graph construction
for the actual restricted maps. Both target coordinates are chosen by the
universal metric uniformization theorem. No branch graph is an input. -/
theorem normalized_local_graph
    {X : CompactComplexSurface} {D : Curve}
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (constant : CovectorGauges.ClassicalZeroDifferentialConstancy)
    (pullbacks : ClassicalPullbackFacts) (unique : TroyanovUniqueness)
    (uniformize : UniformizingDiscCharts)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (f g : Fibration X) (hf : f.Smooth) (hg : g.Smooth)
    (hB : f.Hyperbolic) (hC : g.Hyperbolic) (ν : HolomorphicMap D X)
    (himage : ∀ q : D, ν q ∈ RamificationSupport.ramificationSet f g)
    (hfinite : Fibration.FinitePair f g) (hν : ∃ q r : D, ν q ≠ ν r)
    (gB : ConformalMetric f.base) (gC : ConformalMetric g.base)
    (hBcone : HasConeData gB 0) (hCcone : HasConeData gC 0)
    (hBcurv : HasConstantCurvature gB 0 (-1))
    (hCcurv : HasConstantCurvature gC 0 (-1)) (p : D) :
    ∃ (a : UniformizingDiscChart gB (f (ν p)))
      (d : UniformizingDiscChart gC (g (ν p)))
      (U : Set ℂ), IsOpen U ∧ IsPreconnected U ∧ (chartAt ℂ p) p ∈ U ∧
      ∃ graph : DiscGraphExtension.GlobalDiscIsometry,
        ∀ z ∈ U,
          d.coordinateFunction (CoordinateCalculus.restrictedMap g ν) p z =
            graph (a.coordinateFunction (CoordinateCalculus.restrictedMap f ν) p z) := by
  obtain ⟨hu, _hv, _hD, _hR, _hDiv, hmetric⟩ :=
    CoordinateCalculus.normalized_comparison_complete regularity maps constant pullbacks unique
      f g hf hg hB ν himage hfinite hν gB gC hBcone hCcone hBcurv hCcurv
  obtain ⟨a⟩ := uniformize f.base gB hB hBcone hBcurv (f (ν p))
  obtain ⟨d⟩ := uniformize g.base gC hC hCcone hCcurv (g (ν p))
  obtain ⟨U, hU, hconn, hp, graph, hgraph⟩ := a.local_graph_of_equal_pullbacks d maps extend
    (CoordinateCalculus.restrictedMap f ν) (CoordinateCalculus.restrictedMap g ν) hu p
    a.centre_mem d.centre_mem hmetric
  exact ⟨a, d, U, hU, hconn, hp, graph, hgraph⟩

end Paper27.Geometry.NormalizedBranchConstruction
