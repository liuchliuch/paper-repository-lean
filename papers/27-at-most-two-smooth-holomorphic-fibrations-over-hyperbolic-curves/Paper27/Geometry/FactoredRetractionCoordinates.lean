import Paper27.Geometry.ActualCyclicModels
import Paper27.Geometry.CommonRetractions

/-!
# Actual covering inverse coordinates for fixed factored retractions

The retractions here are arbitrary previously chosen actual retractions.
Their factorization through the two actual unramified curve restrictions
identifies their base coordinates with actual holomorphic local inverses.
No pair-specific retraction is constructed or assumed, and no retraction
normal atlas occurs in the input.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.FactoredRetractionCoordinates

open MetricComparison NormalizedBranchConstruction FixedAmbientBranchGraphs
  RamificationIndexConstancy RetractionFactorization DiscGraphExtension

section CurveCoordinates

variable {C B : Curve} {metric : ConformalMetric B} {b : B}

/-- Validity in fixed actual charts persists near every valid coordinate
point, not just the centre of the selected source chart. -/
theorem valid_eventually_of_valid (a : UniformizingDiscChart metric b)
    (f : HolomorphicMap C B) (i : C) {z : ℂ} (hz : Valid a f i z) :
    ∀ᶠ w in 𝓝 z, Valid a f i w := by
  have hi := (chartAt ℂ i).continuousAt_symm hz.1
  have hf := f.holomorphic.continuous.continuousAt.comp hi
  filter_upwards [(chartAt ℂ i).open_target.mem_nhds hz.1,
    hf.tendsto (a.coordinates.open_source.mem_nhds hz.2)] with w ht hs
  exact ⟨ht, hs⟩

theorem curve_coordinate_analytic (a : UniformizingDiscChart metric b)
    (f : HolomorphicMap C B) (i : C) {z : ℂ} (hz : Valid a f i z) :
    AnalyticAt ℂ (coordinateFunction a f i) z := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [valid_eventually_of_valid a f i hz] with w hw
  exact mdifferentiableAt_iff_differentiableAt.mp
    (coordinateFunction_mdifferentiableAt a f i hw)

theorem curve_coordinate_deriv_ne_zero (a : UniformizingDiscChart metric b)
    (f : HolomorphicMap C B) (i : C) {z : ℂ} (hz : Valid a f i z)
    (hf : Function.Surjective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f ((chartAt ℂ i).symm z))) :
    deriv (coordinateFunction a f i) z ≠ 0 := by
  have hs := (coordinateFunction_surjective_iff a f i hz).mpr hf
  intro hzero
  obtain ⟨v, hv⟩ := hs (1 : ℂ)
  rw [fderiv_eq_deriv_mul, hzero, zero_mul] at hv
  exact zero_ne_one hv

/-- A nonzero inverse derivative follows from the actual inverse identity. -/
theorem inverse_deriv_ne_zero {u : ℂ → ℂ} {q : ℂ} {U : Set ℂ}
    (I : AnalyticInverse u q U) {z : ℂ} (hz : z ∈ I.coordinates.target) :
    deriv I.coordinates.symm z ≠ 0 := by
  have hback := I.coordinates.map_target hz
  have hinverse : u ∘ I.coordinates.symm =ᶠ[𝓝 z] id := by
    exact Filter.eventually_of_mem (I.coordinates.open_target.mem_nhds hz)
      fun t ht => by simpa only [← I.map_eq] using I.coordinates.right_inv ht
  have hchain := (I.analytic _ hback).differentiableAt.hasDerivAt.comp z
    (I.inverse_analytic _ hz).differentiableAt.hasDerivAt
  have hproduct := hchain.unique ((hasDerivAt_id z).congr_of_eventuallyEq hinverse)
  intro hzero
  rw [hzero, mul_zero] at hproduct
  exact zero_ne_one hproduct

end CurveCoordinates

section Retractions

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {f g : Fibration X} {metric : ConformalMetric f.base}

theorem retraction_continuousAt (r : D.Retraction U) (p : D.curve) :
    ContinuousAt r.toFun (D.inclusion p) :=
  (r.holomorphic.mdifferentiableAt (U.open_domain.mem_nhds (U.contains p))).continuousAt

/-- The actual inverse exists in every chosen base chart containing `p`.
Its derivative condition is proved from the actual unramified restriction. -/
theorem restriction_inverse_exists (hf : D.Unramified f) (i p : D.curve)
    (hp : p ∈ D.curve.chartDomain i)
    (a : UniformizingDiscChart metric (f (D.inclusion p))) :
    Nonempty (AnalyticInverse
      (coordinateFunction a (D.restrictedMap f) i) ((chartAt ℂ i) p) Set.univ) := by
  have ht := (chartAt ℂ i).map_source hp
  have hv : Valid a (D.restrictedMap f) i ((chartAt ℂ i) p) := by
    refine ⟨ht, ?_⟩
    rw [(chartAt ℂ i).left_inv hp]
    exact a.centre_mem
  have hs : Function.Surjective
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f)
        ((chartAt ℂ i).symm ((chartAt ℂ i) p))) := by
    rw [(chartAt ℂ i).left_inv hp]
    exact (hf p).2
  exact analyticInverse_exists isOpen_univ (Set.mem_univ _)
    (curve_coordinate_analytic a (D.restrictedMap f) i hv)
    (curve_coordinate_deriv_ne_zero a (D.restrictedMap f) i hv hs)

/-- An existing factored retraction is expressed through the actual local
inverse of the restricted fibration, as a germ on the original surface. -/
theorem retraction_coordinate_germ (r : D.Retraction U) (hfactor : Factorization r f)
    (i p : D.curve) (hp : p ∈ D.curve.chartDomain i)
    (a : UniformizingDiscChart metric (f (D.inclusion p)))
    (I : AnalyticInverse (coordinateFunction a (D.restrictedMap f) i)
      ((chartAt ℂ i) p) Set.univ) :
    (fun q : X => (chartAt ℂ i) (r.toFun q)) =ᶠ[𝓝 (D.inclusion p)]
      fun q => I.coordinates.symm (a.coordinates (f q)) := by
  have hr := retraction_continuousAt r p
  have hchart : ContinuousAt (fun q : X => (chartAt ℂ i) (r.toFun q)) (D.inclusion p) := by
    apply ContinuousAt.comp _ hr
    simpa only [r.retract p] using (chartAt ℂ i).continuousAt hp
  have hvalue : (chartAt ℂ i) (r.toFun (D.inclusion p)) = (chartAt ℂ i) p := by
    rw [r.retract p]
  have hRchart := hchart.tendsto (I.coordinates.open_source.mem_nhds
    (hvalue.symm ▸ I.point_mem))
  have hrsource := hr.tendsto ((chartAt ℂ i).open_source.mem_nhds
    ((r.retract p).symm ▸ hp))
  filter_upwards [hRchart, hrsource, U.open_domain.mem_nhds (U.contains p)] with q hq hqchart hqU
  have hinv := I.coordinates.left_inv hq
  rw [I.map_eq] at hinv
  change I.coordinates.symm
    (a.coordinates (f (D.inclusion ((chartAt ℂ i).symm ((chartAt ℂ i) (r.toFun q)))))) =
      (chartAt ℂ i) (r.toFun q) at hinv
  rw [(chartAt ℂ i).left_inv hqchart] at hinv
  change I.coordinates.symm (a.coordinates (D.restrictedMap f (r.toFun q))) = _ at hinv
  rw [hfactor q hqU] at hinv
  exact hinv.symm

end Retractions

section CyclicCharts

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {f g : Fibration X} {gB : ConformalMetric f.base} {gC : ConformalMetric g.base}
  {hfinite : f.FinitePair g} {hsurj : f.PairSurjective g} {p : D.curve}

theorem surface_first_identity
    (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p))
    (htarget : A.target = ActualCyclicModels.targetChart (D.inclusion p) a d)
    {q : X} (hq : q ∈ A.source.source) :
    a.coordinates (f q) = (A.source q).1 := by
  have h := congrArg Prod.fst (A.identity q hq)
  rw [htarget] at h
  exact h

theorem surface_second_identity
    (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p))
    (htarget : A.target = ActualCyclicModels.targetChart (D.inclusion p) a d)
    {q : X} (hq : q ∈ A.source.source) :
    d.coordinates (g q) = (A.source q).2 ^ A.exponent + A.graph (A.source q).1 := by
  have h := congrArg Prod.snd (A.identity q hq)
  rw [htarget] at h
  exact h

/-- Along the actual embedded critical curve, the two actual restricted
coordinates have the graph germ supplied by the actual cyclic chart. -/
theorem restricted_graph_germ (hD : D.TangentToPair f g)
    (i : D.curve) (hp : p ∈ D.curve.chartDomain i)
    (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p))
    (htarget : A.target = ActualCyclicModels.targetChart (D.inclusion p) a d) :
    coordinateFunction d (D.restrictedMap g) i =ᶠ[𝓝 ((chartAt ℂ i) p)]
      A.graph ∘ coordinateFunction a (D.restrictedMap f) i := by
  have hc := D.inclusion.holomorphic.continuous.continuousAt.comp
    ((chartAt ℂ i).continuousAt_symm ((chartAt ℂ i).map_source hp))
  have hcentre : (D.inclusion ∘ (chartAt ℂ i).symm) ((chartAt ℂ i) p) = D.inclusion p := by
    simp only [Function.comp_apply, (chartAt ℂ i).left_inv hp]
  have hnear := hc.tendsto (A.source.open_source.mem_nhds (hcentre.symm ▸ A.source_mem))
  filter_upwards [hnear] with z hz
  change D.inclusion ((chartAt ℂ i).symm z) ∈ A.source.source at hz
  have hy := (A.axis _ hz).mp (hD ⟨(chartAt ℂ i).symm z, rfl⟩)
  have hfirst := surface_first_identity a d A htarget hz
  have hsecond := surface_second_identity a d A htarget hz
  have hn : A.exponent ≠ 0 := by have hn := A.exponent_ge_two; omega
  rw [hy, zero_pow hn, zero_add, ← hfirst] at hsecond
  exact hsecond

/-- The first retraction in the actual cyclic source coordinates is the
inverse restricted-curve coordinate applied to the first coordinate. -/
theorem first_retraction_germ (r : D.Retraction U) (hfactor : Factorization r f)
    (i : D.curve) (hp : p ∈ D.curve.chartDomain i)
    (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (I : AnalyticInverse (coordinateFunction a (D.restrictedMap f) i)
      ((chartAt ℂ i) p) Set.univ)
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p))
    (htarget : A.target = ActualCyclicModels.targetChart (D.inclusion p) a d) :
    (fun w : ℂ × ℂ => (chartAt ℂ i) (r.toFun (A.source.symm w))) =ᶠ[𝓝 (A.source (D.inclusion p))]
      fun w => I.coordinates.symm w.1 := by
  have ht := A.source.map_source A.source_mem
  have hback : Tendsto A.source.symm (𝓝 (A.source (D.inclusion p))) (𝓝 (D.inclusion p)) := by
    simpa only [A.source.left_inv A.source_mem] using (A.source.continuousAt_symm ht).tendsto
  have hcomp := (retraction_coordinate_germ r hfactor i p hp a I).comp_tendsto hback
  filter_upwards [hcomp, A.source.open_target.mem_nhds ht] with w hw hwt
  have hfirst := surface_first_identity a d A htarget (A.source.map_target hwt)
  rw [A.source.right_inv hwt] at hfirst
  change (chartAt ℂ i) (r.toFun (A.source.symm w)) =
    I.coordinates.symm (a.coordinates (f (A.source.symm w))) at hw
  rw [hfirst] at hw
  exact hw

/-- The second retraction is the other inverse restricted-curve coordinate
applied to the actual cyclic expression. -/
theorem second_retraction_germ (s : D.Retraction U) (hfactor : Factorization s g)
    (i : D.curve) (hp : p ∈ D.curve.chartDomain i)
    (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (I : AnalyticInverse (coordinateFunction d (D.restrictedMap g) i)
      ((chartAt ℂ i) p) Set.univ)
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p))
    (htarget : A.target = ActualCyclicModels.targetChart (D.inclusion p) a d) :
    (fun w : ℂ × ℂ => (chartAt ℂ i) (s.toFun (A.source.symm w))) =ᶠ[𝓝 (A.source (D.inclusion p))]
      fun w => I.coordinates.symm (A.graph w.1 + w.2 ^ A.exponent) := by
  have ht := A.source.map_source A.source_mem
  have hback : Tendsto A.source.symm (𝓝 (A.source (D.inclusion p))) (𝓝 (D.inclusion p)) := by
    simpa only [A.source.left_inv A.source_mem] using (A.source.continuousAt_symm ht).tendsto
  have hcomp := (retraction_coordinate_germ s hfactor i p hp d I).comp_tendsto hback
  filter_upwards [hcomp, A.source.open_target.mem_nhds ht] with w hw hwt
  have hsecond := surface_second_identity a d A htarget (A.source.map_target hwt)
  rw [A.source.right_inv hwt] at hsecond
  change (chartAt ℂ i) (s.toFun (A.source.symm w)) =
    I.coordinates.symm (d.coordinates (g (A.source.symm w))) at hw
  rw [hsecond] at hw
  simpa only [add_comm] using hw

/-- The analytic scalar coordinates needed for the ordinary normal-coordinate
change, retaining the actual retractions and actual cyclic source chart. -/
structure CoordinateData
    (r s : D.Retraction U) (i : D.curve)
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p)) where
  origin : ℂ
  source_centre : A.source (D.inclusion p) = (origin, 0)
  k : ℂ → ℂ
  l : ℂ → ℂ
  k_value : k origin = (chartAt ℂ i) p
  k_analytic : AnalyticAt ℂ k origin
  l_analytic : AnalyticAt ℂ l (A.graph origin)
  graph_analytic : AnalyticAt ℂ A.graph origin
  k_deriv_ne_zero : deriv k origin ≠ 0
  l_deriv_ne_zero : deriv l (A.graph origin) ≠ 0
  graph_relation : l ∘ A.graph =ᶠ[𝓝 origin] k
  first_coordinate : (fun w : ℂ × ℂ => (chartAt ℂ i) (r.toFun (A.source.symm w))) =ᶠ[𝓝 (origin, 0)]
    fun w => k w.1
  second_coordinate : (fun w : ℂ × ℂ => (chartAt ℂ i) (s.toFun (A.source.symm w))) =ᶠ[𝓝 (origin, 0)]
    fun w => l (A.graph w.1 + w.2 ^ A.exponent)

theorem coordinateData_exists (r s : D.Retraction U)
    (hr : Factorization r f) (hs : Factorization s g)
    (hf : D.Unramified f) (hg : D.Unramified g) (hD : D.TangentToPair f g)
    (i : D.curve) (hp : p ∈ D.curve.chartDomain i)
    (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p))
    (htarget : A.target = ActualCyclicModels.targetChart (D.inclusion p) a d) :
    Nonempty (CoordinateData r s i A) := by
  obtain ⟨I⟩ := restriction_inverse_exists hf i p hp a
  obtain ⟨J⟩ := restriction_inverse_exists hg i p hp d
  let χf := coordinateFunction a (D.restrictedMap f) i
  let χg := coordinateFunction d (D.restrictedMap g) i
  let z := (chartAt ℂ i) p
  let u := χf z
  let k : ℂ → ℂ := I.coordinates.symm
  let l : ℂ → ℂ := J.coordinates.symm
  have hfirst : a.coordinates (f (D.inclusion p)) = u := by
    change a.coordinates (f (D.inclusion p)) =
      a.coordinates (f (D.inclusion ((chartAt ℂ i).symm ((chartAt ℂ i) p))))
    rw [(chartAt ℂ i).left_inv hp]
  have hy := (A.axis _ A.source_mem).mp (hD ⟨p, rfl⟩)
  have hcentre : A.source (D.inclusion p) = (u, 0) := by
    apply Prod.ext
    · exact (surface_first_identity a d A htarget A.source_mem).symm.trans hfirst
    · exact hy
  have hcurve := restricted_graph_germ hD i hp a d A htarget
  have hcurve0 : χg z = A.graph u := hcurve.self_of_nhds
  have hItarget : u ∈ I.coordinates.target := by
    simpa only [I.map_eq] using I.coordinates.map_source I.point_mem
  have hJtarget : A.graph u ∈ J.coordinates.target := by
    rw [← hcurve0]
    simpa only [J.map_eq] using J.coordinates.map_source J.point_mem
  have hk0 : k u = z := by
    have h := I.coordinates.left_inv I.point_mem
    rw [I.map_eq] at h
    exact h
  have hkback : Tendsto k (𝓝 u) (𝓝 z) := by
    have h : Tendsto k (𝓝 u) (𝓝 (k u)) := (I.inverse_analytic _ hItarget).continuousAt.tendsto
    rwa [hk0] at h
  have hcurvecomp := hcurve.comp_tendsto hkback
  have hIright : χf ∘ k =ᶠ[𝓝 u] id := by
    apply Filter.eventually_of_mem (I.coordinates.open_target.mem_nhds hItarget)
    intro t ht
    have h := I.coordinates.right_inv ht
    rw [I.map_eq] at h
    exact h
  have hJleft : l ∘ χg =ᶠ[𝓝 z] id := by
    apply Filter.eventually_of_mem (J.coordinates.open_source.mem_nhds J.point_mem)
    intro t ht
    have h := J.coordinates.left_inv ht
    rw [J.map_eq] at h
    exact h
  have hJcomp := hJleft.comp_tendsto hkback
  have hrelation : l ∘ A.graph =ᶠ[𝓝 u] k := by
    filter_upwards [hcurvecomp, hIright, hJcomp] with t hgraph hright hleft
    change χg (k t) = A.graph (χf (k t)) at hgraph
    change χf (k t) = t at hright
    change l (χg (k t)) = k t at hleft
    change l (A.graph t) = k t
    rw [hright] at hgraph
    rw [← hgraph, hleft]
  refine ⟨{ origin := u
            source_centre := hcentre
            k := k
            l := l
            k_value := hk0
            k_analytic := I.inverse_analytic _ hItarget
            l_analytic := J.inverse_analytic _ hJtarget
            graph_analytic := ?_
            k_deriv_ne_zero := inverse_deriv_ne_zero I hItarget
            l_deriv_ne_zero := inverse_deriv_ne_zero J hJtarget
            graph_relation := hrelation
            first_coordinate := ?_
            second_coordinate := ?_ }⟩
  · simpa only [hcentre] using A.graph_analytic _ A.source_mem
  · simpa only [hcentre] using first_retraction_germ r hr i hp a d I A htarget
  · simpa only [hcentre] using second_retraction_germ s hs i hp a d J A htarget

end CyclicCharts

end Paper27.Geometry.FactoredRetractionCoordinates
