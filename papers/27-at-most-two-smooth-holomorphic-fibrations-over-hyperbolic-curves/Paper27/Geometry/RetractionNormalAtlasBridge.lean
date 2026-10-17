import Paper27.Geometry.FactoredRetractionCoordinates
import Paper27.Geometry.RetractionNormalCoordinates
import Paper27.Geometry.RetractionCoordinateGerms
import Paper27.Geometry.CurveBranchInputs

/-!
# From fixed factored retractions to their actual normal atlas

Actual covering inverse coordinates supply the scalar analytic functions.
The ordinary analytic coordinate change straightens them. Composition with
the actual surface chart and restriction to an actual open neighbourhood
then gives the precise normal-form chart for the previously chosen pair of
retractions. All source neighbourhoods lie in their common given domain.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.RetractionNormalAtlasBridge

open MetricComparison NormalizedBranchConstruction FixedAmbientBranchGraphs
  RamificationIndexConstancy RetractionFactorization FactoredRetractionCoordinates
  RetractionNormalCoordinates

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r s : D.Retraction U} {f g : Fibration X}
  {hfinite : f.FinitePair g} {hsurj : f.PairSurjective g}

/-- The actual normal chart at a specified point in a specified base chart. -/
structure CenteredNormalChart (D : EmbeddedCurve X) (U : D.Neighbourhood)
    (r s : D.Retraction U) (n : ℕ) (i p : D.curve) where
  chart : RetractionAtlas.NormalFormChart D.curve r.toFun s.toFun n i
  source_mem : D.inclusion p ∈ chart.coordinates.source
  centre : chart.coordinates (D.inclusion p) = ((chartAt ℂ i) p, 0)
  source_subset : chart.coordinates.source ⊆ U.domain
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    chart.coordinates chart.coordinates.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    chart.coordinates.symm chart.coordinates.target

/-- All germ identities can be imposed on one actual open source
neighbourhood, so the resulting chart has the exact normal identities. -/
theorem centeredChart_of_coordinateData {i p : D.curve}
    (hp : p ∈ D.curve.chartDomain i)
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p)) (C : CoordinateData r s i A)
    (E : StraightenedPair C.k C.l A.graph A.exponent C.origin) :
    Nonempty (CenteredNormalChart D U r s A.exponent i p) := by
  let x := D.inclusion p
  have hsource : Tendsto A.source (𝓝 x) (𝓝 (C.origin, 0)) := by
    rw [← C.source_centre]
    exact (A.source.continuousAt A.source_mem).tendsto
  have hRcomp := C.first_coordinate.comp_tendsto hsource
  have hScomp := C.second_coordinate.comp_tendsto hsource
  have hR : ∀ᶠ q in 𝓝 x, (chartAt ℂ i) (r.toFun q) = C.k (A.source q).1 := by
    filter_upwards [hRcomp, A.source.open_source.mem_nhds A.source_mem] with q hq hsourceq
    change (chartAt ℂ i) (r.toFun (A.source.symm (A.source q))) = _ at hq
    rwa [A.source.left_inv hsourceq] at hq
  have hS : ∀ᶠ q in 𝓝 x, (chartAt ℂ i) (s.toFun q) =
      C.l (A.graph (A.source q).1 + (A.source q).2 ^ A.exponent) := by
    filter_upwards [hScomp, A.source.open_source.mem_nhds A.source_mem] with q hq hsourceq
    change (chartAt ℂ i) (s.toFun (A.source.symm (A.source q))) = _ at hq
    rwa [A.source.left_inv hsourceq] at hq
  have hrbase := (retraction_continuousAt r p).tendsto
    ((chartAt ℂ i).open_source.mem_nhds ((r.retract p).symm ▸ hp))
  have hsbase := (retraction_continuousAt s p).tendsto
    ((chartAt ℂ i).open_source.mem_nhds ((s.retract p).symm ▸ hp))
  have hgood : {q | q ∈ U.domain ∧ r.toFun q ∈ D.curve.chartDomain i ∧
      s.toFun q ∈ D.curve.chartDomain i ∧
      (chartAt ℂ i) (r.toFun q) = C.k (A.source q).1 ∧
      (chartAt ℂ i) (s.toFun q) =
        C.l (A.graph (A.source q).1 + (A.source q).2 ^ A.exponent)} ∈ 𝓝 x := by
    filter_upwards [U.open_domain.mem_nhds (U.contains p), hrbase, hsbase, hR, hS]
      with q hq hrq hsq hRq hSq
    exact ⟨hq, hrq, hsq, hRq, hSq⟩
  obtain ⟨V, hVgood, hVopen, hxV⟩ := mem_nhds_iff.mp hgood
  let e := (A.source.trans E.coordinate.chart).restrOpen V hVopen
  have hE : E.coordinate.chart.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) := by
    constructor
    · intro z hz
      exact (mdifferentiableAt_iff_differentiableAt.mpr
        (E.coordinate.analytic z hz).differentiableAt).mdifferentiableWithinAt
    · intro z hz
      exact (mdifferentiableAt_iff_differentiableAt.mpr
        (E.coordinate.inverse_analytic z hz).differentiableAt).mdifferentiableWithinAt
  have hA : A.source.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) :=
    ⟨A.source_holomorphic, A.source_inverse_holomorphic⟩
  have hmd := hA.trans hE
  refine ⟨{
    chart := {
      coordinates := e
      r_source := fun q hq => (hVgood hq.2).2.1
      s_source := fun q hq => (hVgood hq.2).2.2.1
      r_normal := ?_
      s_normal := ?_
    }
    source_mem := ?_
    centre := ?_
    source_subset := fun q hq => (hVgood hq.2).1
    holomorphic := ?_
    inverse_holomorphic := ?_
  }⟩
  · intro q hq
    exact (hVgood hq.2).2.2.2.1.trans (E.first (A.source q) hq.1.2).symm
  · intro q hq
    exact (hVgood hq.2).2.2.2.2.trans (E.second (A.source q) hq.1.2)
  · refine ⟨⟨A.source_mem, ?_⟩, hxV⟩
    change A.source (D.inclusion p) ∈ E.coordinate.chart.source
    rw [C.source_centre]
    exact E.coordinate.source_mem
  · change E.coordinate.chart (A.source (D.inclusion p)) = ((chartAt ℂ i) p, 0)
    rw [C.source_centre, E.centre, C.k_value]
  · intro q hq
    exact (hmd.mdifferentiableAt hq.1).mdifferentiableWithinAt
  · intro z hz
    exact (hmd.mdifferentiableAt_symm hz.1).mdifferentiableWithinAt

theorem centeredChart_exists {gB : ConformalMetric f.base} {gC : ConformalMetric g.base}
    (division : AnalyticDividedDifferences) (roots : AnalyticUnitRoots)
    (hr : Factorization r f) (hs : Factorization s g)
    (hf : D.Unramified f) (hg : D.Unramified g) (hD : D.TangentToPair f g)
    (i p : D.curve) (hp : p ∈ D.curve.chartDomain i)
    (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
      (D.inclusion p))
    (htarget : A.target = ActualCyclicModels.targetChart (D.inclusion p) a d) :
    Nonempty (CenteredNormalChart D U r s A.exponent i p) := by
  obtain ⟨C⟩ := coordinateData_exists r s hr hs hf hg hD i hp a d A htarget
  obtain ⟨E⟩ := straightenedPair_exists division roots (n := A.exponent)
    (by have hn := A.exponent_ge_two; omega)
    C.k_analytic C.l_analytic C.graph_analytic C.k_deriv_ne_zero C.l_deriv_ne_zero C.graph_relation
  exact centeredChart_of_coordinateData hp A C E

/-- The irrelevant entries of the atlas, where the requested point is not
in the requested base domain, have empty actual source and target. -/
def emptyNormalChart (n : ℕ) (i : D.curve) :
    RetractionAtlas.NormalFormChart D.curve r.toFun s.toFun n i where
  coordinates := (chartAt (ℂ × ℂ) (D.inclusion D.curve.basepoint)).restrOpen ∅ isOpen_empty
  r_source := fun _ h => False.elim h.2
  s_source := fun _ h => False.elim h.2
  r_normal := fun _ h => False.elim h.2
  s_normal := fun _ h => False.elim h.2

theorem emptyNormalChart_holomorphic (n : ℕ) (i : D.curve) :
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      (emptyNormalChart (r := r) (s := s) n i).coordinates
      (emptyNormalChart (r := r) (s := s) n i).coordinates.source :=
  fun _ h => False.elim h.2

theorem emptyNormalChart_inverse_holomorphic (n : ℕ) (i : D.curve) :
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      (emptyNormalChart (r := r) (s := s) n i).coordinates.symm
      (emptyNormalChart (r := r) (s := s) n i).coordinates.target :=
  fun _ h => False.elim h.2

/-- Pointwise actual centred charts assemble into the exact atlas interface.
No compatibility law is assumed; later compatibility follows from the two
actual retraction identities in every chart. -/
theorem normalAtlas_of_centered (n : ℕ)
    (hcharts : ∀ i p : D.curve, p ∈ D.curve.chartDomain i →
      Nonempty (CenteredNormalChart D U r s n i p)) :
    Nonempty (RetractionCoordinateGerms.NormalAtlas D U r s n) := by
  classical
  let chosen : ∀ i p : D.curve, p ∈ D.curve.chartDomain i →
      CenteredNormalChart D U r s n i p := fun i p hp => Classical.choice (hcharts i p hp)
  let charts : ∀ i p : D.curve, RetractionAtlas.NormalFormChart D.curve r.toFun s.toFun n i :=
    fun i p => if hp : p ∈ D.curve.chartDomain i then (chosen i p hp).chart else emptyNormalChart n i
  refine ⟨{ chart := charts
            source_mem := ?_
            centre := ?_
            source_subset := ?_
            holomorphic := ?_
            inverse_holomorphic := ?_ }⟩
  · intro i p hp
    dsimp only [charts]
    rw [dif_pos hp]
    exact (chosen i p hp).source_mem
  · intro i p hp
    dsimp only [charts]
    rw [dif_pos hp]
    exact (chosen i p hp).centre
  · intro i p q hq
    dsimp only [charts] at hq
    split_ifs at hq with hp
    · exact (chosen i p hp).source_subset hq
    · exact False.elim hq.2
  · intro i p
    dsimp only [charts]
    split_ifs with hp
    · exact (chosen i p hp).holomorphic
    · exact emptyNormalChart_holomorphic n i
  · intro i p
    dsimp only [charts]
    split_ifs with hp
    · exact (chosen i p hp).inverse_holomorphic
    · exact emptyNormalChart_inverse_holomorphic n i

/-- Actual surface cyclic charts of uniform index give a normal atlas for
any already selected pair of factored retractions on their common domain. -/
theorem normalAtlas_of_pair_models
    {gB : ConformalMetric f.base} {gC : ConformalMetric g.base}
    (division : AnalyticDividedDifferences) (roots : AnalyticUnitRoots)
    (hr : Factorization r f) (hs : Factorization s g)
    (hf : D.Unramified f) (hg : D.Unramified g) (hD : D.TangentToPair f g) (n : ℕ)
    (models : ∀ p : D.curve,
      ∃ (a : UniformizingDiscChart gB (f (D.inclusion p)))
        (d : UniformizingDiscChart gC (g (D.inclusion p)))
        (A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
          (D.inclusion p)),
        A.target = ActualCyclicModels.targetChart (D.inclusion p) a d ∧ A.exponent = n) :
    Nonempty (RetractionCoordinateGerms.NormalAtlas D U r s n) := by
  apply normalAtlas_of_centered n
  intro i p hp
  obtain ⟨a, d, A, htarget, hindex⟩ := models p
  have hchart := centeredChart_exists division roots hr hs hf hg hD i p hp a d A htarget
  simpa only [hindex] using hchart

/-- The original paired fibrations and generic classical inputs now produce
an actual normal atlas for arbitrary already chosen factored retractions.
The uniform index is derived from local degree and connectedness, not
assumed as a geometric field. -/
theorem normalAtlas_of_original_pair
    (K : CurveBranchInputs) (degrees : FiniteLocalDegreeTheory)
    (division : AnalyticDividedDifferences) (roots : AnalyticUnitRoots)
    (hf : f.Smooth) (hg : g.Smooth) (hB : f.Hyperbolic) (hC : g.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (hD : D.TangentToPair f g) (hr : Factorization r f) (hs : Factorization s g) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty (RetractionCoordinateGerms.NormalAtlas D U r s n) ∧
      ∀ p : D.curve,
        ∀ A : SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj)
          (D.inclusion p), A.exponent = n := by
  let q := RamificationSupport.finiteSurjectivePair f g hfinite hsurj
  have charts : ∀ x ∈ criticalSet q, Nonempty (SurfaceCyclicChart q x) := by
    intro x hx
    obtain ⟨a, d, B, hn, hvalid⟩ := K.euclidean_model_exists f g hf hg hB hC hfinite hsurj N x hx
    exact ⟨ActualCyclicModels.surfaceChartOfModel hfinite hsurj x hx a d B hn hvalid⟩
  obtain ⟨n, hn, _hdegree, hindex⟩ := component_index_constant degrees q D hD charts
  have hunram := K.unramified_of_tangency f g hf hg hB hC hfinite hsurj N D hD
  have models : ∀ p : D.curve,
      ∃ (a : UniformizingDiscChart (K.metrics.metric f.base) (f (D.inclusion p)))
        (d : UniformizingDiscChart (K.metrics.metric g.base) (g (D.inclusion p)))
        (A : SurfaceCyclicChart q (D.inclusion p)),
        A.target = ActualCyclicModels.targetChart (D.inclusion p) a d ∧ A.exponent = n := by
    intro p
    obtain ⟨a, d, B, hBindex, hvalid⟩ := K.euclidean_model_exists f g hf hg hB hC hfinite hsurj N
      (D.inclusion p) (hD ⟨p, rfl⟩)
    let A := ActualCyclicModels.surfaceChartOfModel hfinite hsurj (D.inclusion p)
      (hD ⟨p, rfl⟩) a d B hBindex hvalid
    exact ⟨a, d, A, rfl, hindex p A⟩
  exact ⟨n, hn, normalAtlas_of_pair_models division roots hr hs hunram.1 hunram.2 hD n models,
    hindex⟩

end Paper27.Geometry.RetractionNormalAtlasBridge
