import Paper27.Geometry.BranchGraphs
import Paper27.Geometry.MetricComparison
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv

/-!
# Extending the metric graph across a ramification point

The inverse function theorem below is proved using mathlib. The candidate
regular graph is the actual function v ∘ u⁻¹, and its metric identity is
calculated from the two equal pullback densities. Only the classical extension
of a local Poincaré isometry to an isometry of the whole disc is an explicit
external input. The identity theorem then extends the graph over a possibly
ramified centre of the two original maps.
-/
noncomputable section
open scoped Topology
open Filter
namespace Paper27.Geometry.DiscGraphExtension
open BranchGraphs

/-- A local inverse, including analyticity of the actual inverse function. -/
structure AnalyticInverse (u : ℂ → ℂ) (q : ℂ) (U : Set ℂ) where
  coordinates : OpenPartialHomeomorph ℂ ℂ
  map_eq : (coordinates : ℂ → ℂ) = u
  point_mem : q ∈ coordinates.source
  source_subset : coordinates.source ⊆ U
  analytic : AnalyticOnNhd ℂ u coordinates.source
  inverse_analytic : AnalyticOnNhd ℂ coordinates.symm coordinates.target

/-- No unformalized inverse function theorem is needed here. We restrict the
actual partial homeomorphism to a neighbourhood where u is analytic with
nonzero derivative, and use mathlib's analytic inverse theorem pointwise. -/
theorem analyticInverse_exists {u : ℂ → ℂ} {q : ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hq : q ∈ U) (hu : AnalyticAt ℂ u q)
    (hd : deriv u q ≠ 0) : Nonempty (AnalyticInverse u q U) := by
  have hs : HasStrictDerivAt u (deriv u q) q := hu.hasStrictFDerivAt.hasStrictDerivAt
  let e := (hs.hasStrictFDerivAt_equiv hd).toOpenPartialHomeomorph u
  have he : (e : ℂ → ℂ) = u := rfl
  have hnear : {x | x ∈ U ∧ AnalyticAt ℂ u x ∧ deriv u x ≠ 0} ∈ 𝓝 q := by
    filter_upwards [hU.mem_nhds hq, hu.eventually_analyticAt,
      hu.deriv.continuousAt.eventually_ne hd] with x hx hax hdx
    exact ⟨hx, hax, hdx⟩
  obtain ⟨V, hVsub, hVopen, hqV⟩ := mem_nhds_iff.mp hnear
  let e' := e.restrOpen V hVopen
  have he' : (e' : ℂ → ℂ) = u := rfl
  refine ⟨{ coordinates := e'
            map_eq := he'
            point_mem := ?_
            source_subset := ?_
            analytic := ?_
            inverse_analytic := ?_ }⟩
  · exact ⟨(hs.hasStrictFDerivAt_equiv hd).mem_toOpenPartialHomeomorph_source, hqV⟩
  · intro x hx
    exact (hVsub hx.2).1
  · intro x hx
    exact (hVsub hx.2).2.1
  · intro y hy
    have hx := e'.map_target hy
    have hax := (hVsub hx.2).2.1
    have hdx := (hVsub hx.2).2.2
    apply e'.analyticAt_symm hy
    · simpa only [he'] using hax
    · exact hax.differentiableAt.hasDerivAt.hasFDerivAt_equiv hdx |>.fderiv

/-- A global analytic Poincaré isometry on the unit disc. This is a function
with the actual density identity, rather than an abstract graph label. -/
structure GlobalDiscIsometry where
  toFun : ℂ → ℂ
  analytic : AnalyticOnNhd ℂ toFun (Metric.ball 0 1)
  maps_disc : ∀ z : ℂ, ‖z‖ < 1 → ‖toFun z‖ < 1
  metric_identity : ∀ z : ℂ, ‖z‖ < 1 →
    poincareDensity (toFun z) * ‖deriv toFun z‖ ^ 2 = poincareDensity z

instance : CoeFun GlobalDiscIsometry (fun _ => ℂ → ℂ) := ⟨fun A => A.toFun⟩

/-- Classical local-to-global extension for the simply connected complete
Poincaré disc (equivalently, classification of orientation-preserving
hyperbolic isometries by disc automorphisms). This universal interface does
not mention ramified maps, their image, or normalized branches. -/
def LocalDiscIsometryExtension : Prop :=
  ∀ (z : ℂ) (φ : LocalDiscIsometry z), ∃ A : GlobalDiscIsometry,
    φ.toFun =ᶠ[𝓝 z] A.toFun

/-- The inverse derivative chain rule gives the metric identity for v∘u⁻¹.
All functions and derivatives are actual complex functions. -/
theorem inverse_graph_metric {u v i : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℂ u (i z)) (hv : DifferentiableAt ℂ v (i z))
    (hi : DifferentiableAt ℂ i z)
    (hinv : u ∘ i =ᶠ[𝓝 z] id)
    (hmetric : poincareDensity (u (i z)) * ‖deriv u (i z)‖ ^ 2 =
      poincareDensity (v (i z)) * ‖deriv v (i z)‖ ^ 2) :
    poincareDensity ((v ∘ i) z) * ‖deriv (v ∘ i) z‖ ^ 2 = poincareDensity z := by
  have hc : deriv u (i z) * deriv i z = 1 := by
    have hh := hu.hasDerivAt.comp z hi.hasDerivAt
    exact hh.unique ((hasDerivAt_id z).congr_of_eventuallyEq hinv)
  have hvcomp := hv.hasDerivAt.comp z hi.hasDerivAt
  have hn : ‖deriv u (i z)‖ ^ 2 * ‖deriv i z‖ ^ 2 = 1 := by
    rw [← mul_pow, ← norm_mul, hc, norm_one, one_pow]
  have heq : u (i z) = z := hinv.self_of_nhds
  rw [Function.comp_apply, hvcomp.deriv, norm_mul, mul_pow, ← mul_assoc,
    ← hmetric, heq]
  calc
    poincareDensity z * ‖deriv u (i z)‖ ^ 2 * ‖deriv i z‖ ^ 2 =
        poincareDensity z * (‖deriv u (i z)‖ ^ 2 * ‖deriv i z‖ ^ 2) := by ring
    _ = poincareDensity z := by rw [hn, mul_one]

/-- Construct the actual local hyperbolic graph on a regular inverse chart. -/
def regularGraph {u v : ℂ → ℂ} {q : ℂ} {U : Set ℂ}
    (i : AnalyticInverse u q U)
    (hv : AnalyticOnNhd ℂ v U)
    (hudisc : ∀ z ∈ U, ‖u z‖ < 1) (hvdisc : ∀ z ∈ U, ‖v z‖ < 1)
    (hmetric : ∀ z ∈ U,
      poincareDensity (u z) * ‖deriv u z‖ ^ 2 =
        poincareDensity (v z) * ‖deriv v z‖ ^ 2) :
    LocalDiscIsometry (u q) where
  toFun := v ∘ i.coordinates.symm
  domain := i.coordinates.target
  open_domain := i.coordinates.open_target
  centre_mem := by simpa only [← i.map_eq] using i.coordinates.map_source i.point_mem
  domain_disc z hz := by
    have hs := i.coordinates.map_target hz
    have h := hudisc _ (i.source_subset hs)
    simpa only [← i.map_eq, i.coordinates.right_inv hz] using h
  maps_disc z hz := hvdisc _ (i.source_subset (i.coordinates.map_target hz))
  analytic z hz := (hv _ (i.source_subset (i.coordinates.map_target hz))).comp
    (i.inverse_analytic z hz)
  metric_identity z hz := by
    have hs := i.coordinates.map_target hz
    apply inverse_graph_metric (i.analytic _ hs).differentiableAt
      (hv _ (i.source_subset hs)).differentiableAt (i.inverse_analytic z hz).differentiableAt
    · have hinv := i.coordinates.eventually_right_inverse' hs
      simpa only [i.coordinates.right_inv hz, i.map_eq, Function.comp_def] using hinv
    · exact hmetric _ (i.source_subset hs)

/-- Equal pullback metrics give one analytic graph on the whole connected
source chart, including its ramification points. The regular inverse and the
graph are constructed; only the universal disc extension theorem is an input. -/
theorem graph_across_ramification (extend : LocalDiscIsometryExtension)
    {u v : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hconn : IsPreconnected U)
    (hu : AnalyticOnNhd ℂ u U) (hv : AnalyticOnNhd ℂ v U)
    (hudisc : ∀ z ∈ U, ‖u z‖ < 1) (hvdisc : ∀ z ∈ U, ‖v z‖ < 1)
    (hmetric : ∀ z ∈ U,
      poincareDensity (u z) * ‖deriv u z‖ ^ 2 =
        poincareDensity (v z) * ‖deriv v z‖ ^ 2)
    (regular : ℂ) (hr : regular ∈ U) (hd : deriv u regular ≠ 0) :
    ∃ A : GlobalDiscIsometry, ∀ z ∈ U, v z = A (u z) := by
  obtain ⟨i⟩ := analyticInverse_exists hU hr (hu regular hr) hd
  let φ := regularGraph i hv hudisc hvdisc hmetric
  obtain ⟨A, hA⟩ := extend (u regular) φ
  have hregular : v =ᶠ[𝓝 regular] A.toFun ∘ u := by
    have hleft := i.coordinates.eventually_left_inverse i.point_mem
    have hcompose := hA.comp_tendsto (hu regular hr).continuousAt
    filter_upwards [hleft, hcompose] with z hz hAz
    change (v ∘ i.coordinates.symm) (u z) = A (u z) at hAz
    have hz' : i.coordinates.symm (u z) = z := by simpa only [i.map_eq] using hz
    simpa only [Function.comp_apply, hz'] using hAz
  refine ⟨A, ?_⟩
  have hAu : AnalyticOnNhd ℂ (A.toFun ∘ u) U := by
    intro z hz
    apply (A.analytic (u z) ?_).comp (hu z hz)
    simpa only [Metric.mem_ball, dist_zero_right] using hudisc z hz
  exact hv.eqOn_of_preconnected_of_eventuallyEq hAu hconn hr hregular

end Paper27.Geometry.DiscGraphExtension
