import Paper27.Geometry.CurveBranchInputs

/-!
# Lemma 2.3 for arbitrary actual curve maps

Equality of the actual derivative-zero divisors gives equality of actual
pullback metrics. At every point, including a ramified point, the actual
image lies in an isometry graph in actual uniformizing charts on an actual
open neighbourhood of the source curve. No regularity assumption is imposed
on the point at which the conclusion is requested.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry
open MetricComparison NormalizedBranchConstruction

structure LocalIsometryGraph {D B C : Curve} (u : HolomorphicMap D B)
    (v : HolomorphicMap D C) (gB : ConformalMetric B) (gC : ConformalMetric C) (p : D) where
  firstChart : UniformizingDiscChart gB (u p)
  secondChart : UniformizingDiscChart gC (v p)
  graph : DiscGraphExtension.GlobalDiscIsometry
  neighbourhood : Set D
  open_neighbourhood : IsOpen neighbourhood
  point_mem : p ∈ neighbourhood
  first_mem : ∀ q ∈ neighbourhood, u q ∈ firstChart.coordinates.source
  second_mem : ∀ q ∈ neighbourhood, v q ∈ secondChart.coordinates.source
  identity : ∀ q ∈ neighbourhood,
    secondChart.coordinates (v q) = graph (firstChart.coordinates (u q))

namespace CurveBranchInputs
variable (K : CurveBranchInputs)
include K

/-- The graph statement on the actual source manifold, rather than only on
an unassociated scalar disc. The scalar graph constructed across the
ramification centre is transported through the actual source chart. -/
theorem local_isometry_graph {D B C : Curve} (u : HolomorphicMap D B)
    (v : HolomorphicMap D C) (hu : Nonconstant u) (hB : B.Hyperbolic) (hC : C.Hyperbolic)
    (hmetric : pullback u (K.metrics.metric B) = pullback v (K.metrics.metric C)) (p : D) :
    Nonempty (LocalIsometryGraph u v (K.metrics.metric B) (K.metrics.metric C) p) := by
  obtain ⟨a⟩ := K.uniformizingCharts B (K.metrics.metric B) hB (K.metrics.cone B hB)
    (K.metrics.curvature B hB) (u p)
  obtain ⟨d⟩ := K.uniformizingCharts C (K.metrics.metric C) hC (K.metrics.cone C hC)
    (K.metrics.curvature C hC) (v p)
  obtain ⟨U, hU, _hconn, hp, graph, hgraph⟩ := a.local_graph_of_equal_pullbacks d K.curveMaps
    K.discExtension u v hu p a.centre_mem d.centre_mem hmetric
  let V : Set D := ((chartAt ℂ p).source ∩ (chartAt ℂ p) ⁻¹' U) ∩
    (u ⁻¹' a.coordinates.source ∩ v ⁻¹' d.coordinates.source)
  have hV : IsOpen V := by
    apply IsOpen.inter
    · exact (chartAt ℂ p).continuousOn_toFun.isOpen_inter_preimage (chartAt ℂ p).open_source hU
    · exact (a.coordinates.open_source.preimage u.holomorphic.continuous).inter
        (d.coordinates.open_source.preimage v.holomorphic.continuous)
  refine ⟨{ firstChart := a
            secondChart := d
            graph := graph
            neighbourhood := V
            open_neighbourhood := hV
            point_mem := ⟨⟨mem_chart_source ℂ p, hp⟩, a.centre_mem, d.centre_mem⟩
            first_mem := fun q hq => hq.2.1
            second_mem := fun q hq => hq.2.2
            identity := ?_ }⟩
  intro q hq
  have he := hgraph ((chartAt ℂ p) q) hq.1.2
  simpa only [UniformizingDiscChart.coordinateFunction, Function.comp_apply,
    (chartAt ℂ p).left_inv hq.1.1] using he

/-- Lemma 2.3 with the actual effective ramification divisors as its premise.
The metric and graph are both conclusions, for arbitrary nonconstant maps. -/
theorem curve_metric_rigidity {D B C : Curve} (u : HolomorphicMap D B)
    (v : HolomorphicMap D C) (hu : Nonconstant u) (hv : Nonconstant v)
    (hB : B.Hyperbolic) (hC : C.Hyperbolic)
    (hR : ramificationDivisor u (K.curveMaps.ramification_finite D B u hu) =
      ramificationDivisor v (K.curveMaps.ramification_finite D C v hv)) :
    pullback u (K.metrics.metric B) = pullback v (K.metrics.metric C) ∧
      ∀ p : D, Nonempty (LocalIsometryGraph u v (K.metrics.metric B) (K.metrics.metric C) p) := by
  have horders : ∀ p, ramificationOrder u p = ramificationOrder v p :=
    fun p => congrArg (fun R : D →₀ ℕ => R p) hR
  have hmetric := pullback_metrics_equal K.curveMaps K.pullbacks K.negativeCurvatureUniqueness
    u v hu hv hB (K.metrics.metric B) (K.metrics.metric C)
    (K.metrics.cone B hB) (K.metrics.cone C hC)
    (K.metrics.curvature B hB) (K.metrics.curvature C hC) horders
  exact ⟨hmetric, K.local_isometry_graph u v hu hB hC hmetric⟩

end CurveBranchInputs
end Paper27.Geometry
