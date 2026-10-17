import Paper27.Geometry.NormalizedBranchConstruction
import Paper27.Geometry.FiniteAnalyticGerm

/-!
# Normalized graphs in fixed ambient and uniformizing coordinates

The target uniformizing charts are fixed before choosing a normalization
branch. All branches through the same source point consequently have the
same actual ambient coordinate functions `F,G`. Actual chart derivatives
transport submersion and joint ramification conditions. Composition germs
transport the metric equality and the nonconstant derivative order. Thus
the branch graph is constructed, rather than supplied as geometric data.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.FixedAmbientBranchGraphs

open NormalizedBranchConstruction MetricComparison

section Coordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : CompactComplexManifold E} {B : Curve} {gB : ConformalMetric B} {b : B}

/-- The actual source chart is fixed at `x`; the actual uniformizing target
chart is fixed independently of a choice of normalization branch. -/
def coordinateFunction (a : UniformizingDiscChart gB b) (f : HolomorphicMap M B)
    (x : M) : E → ℂ := a.coordinates ∘ f ∘ (chartAt E x).symm

def Valid (a : UniformizingDiscChart gB b) (f : HolomorphicMap M B)
    (x : M) (z : E) : Prop :=
  z ∈ (chartAt E x).target ∧ f ((chartAt E x).symm z) ∈ a.coordinates.source

theorem valid_eventually (a : UniformizingDiscChart gB b) (f : HolomorphicMap M B)
    (x : M) (hx : f x ∈ a.coordinates.source) :
    ∀ᶠ z in 𝓝 ((chartAt E x) x), Valid a f x z := by
  have hi := (chartAt E x).continuousAt_symm
    ((chartAt E x).map_source (mem_chart_source E x))
  have hf := f.holomorphic.continuous.continuousAt.comp hi
  have hcentre : (f ∘ (chartAt E x).symm) ((chartAt E x) x) = f x := by
    simp only [Function.comp_apply, (chartAt E x).left_inv (mem_chart_source E x)]
  have ht := hf.tendsto (a.coordinates.open_source.mem_nhds (hcentre.symm ▸ hx))
  filter_upwards [ht, (chartAt E x).open_target.mem_nhds
    ((chartAt E x).map_source (mem_chart_source E x))] with z hz hzt
  exact ⟨hzt, hz⟩

theorem coordinateFunction_mdifferentiableAt (a : UniformizingDiscChart gB b)
    (f : HolomorphicMap M B) (x : M) {z : E} (hz : Valid a f x z) :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (coordinateFunction a f x) z :=
  (a.mdifferentiable.mdifferentiableAt hz.2).comp z
    ((f.holomorphic _).comp z
      ((mdifferentiable_chart (I := 𝓘(ℂ, E)) x).mdifferentiableAt_symm hz.1))

theorem coordinateFunction_derivative (a : UniformizingDiscChart gB b)
    (f : HolomorphicMap M B) (x : M) {z : E} (hz : Valid a f x z) :
    fderiv ℂ (coordinateFunction a f x) z =
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) a.coordinates (f ((chartAt E x).symm z))).comp
        ((mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f ((chartAt E x).symm z)).comp
          (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E x).symm z)) := by
  have hi := (mdifferentiable_chart (I := 𝓘(ℂ, E)) x).mdifferentiableAt_symm hz.1
  rw [← mfderiv_eq_fderiv]
  unfold coordinateFunction
  rw [mfderiv_comp z (a.mdifferentiable.mdifferentiableAt hz.2)
    ((f.holomorphic _).comp z hi), mfderiv_comp z (f.holomorphic _) hi]
  rfl

theorem coordinateFunction_surjective_iff (a : UniformizingDiscChart gB b)
    (f : HolomorphicMap M B) (x : M) {z : E} (hz : Valid a f x z) :
    Function.Surjective (fderiv ℂ (coordinateFunction a f x) z) ↔
      Function.Surjective (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f ((chartAt E x).symm z)) := by
  let A : E ≃L[ℂ] E :=
    (mdifferentiable_chart (I := 𝓘(ℂ, E)) x).symm.mfderiv hz.1
  let T : ℂ ≃L[ℂ] ℂ := a.mdifferentiable.mfderiv hz.2
  let L := mfderiv 𝓘(ℂ, E) 𝓘(ℂ, ℂ) f ((chartAt E x).symm z)
  rw [coordinateFunction_derivative a f x hz]
  change Function.Surjective (fun v => T (L (A v))) ↔ Function.Surjective L
  constructor
  · intro h y
    obtain ⟨v, hv⟩ := h (T y)
    exact ⟨A v, T.injective hv⟩
  · intro h y
    obtain ⟨v, hv⟩ := h (T.symm y)
    refine ⟨A.symm v, ?_⟩
    simpa only [A.apply_symm_apply, T.apply_symm_apply] using congrArg T hv

theorem coordinateFunction_disc (a : UniformizingDiscChart gB b)
    (f : HolomorphicMap M B) (x : M) {z : E} (hz : Valid a f x z) :
    ‖coordinateFunction a f x z‖ < 1 :=
  a.target_disc _ (a.coordinates.map_source hz.2)

theorem coordinateFunction_continuousAt (a : UniformizingDiscChart gB b)
    (f : HolomorphicMap M B) (x : M) {z : E} (hz : Valid a f x z) :
    ContinuousAt (coordinateFunction a f x) z :=
  (coordinateFunction_mdifferentiableAt a f x hz).continuousAt

end Coordinates

section SurfaceCoordinates

variable {X : CompactComplexSurface} {B C : Curve}
  {gB : ConformalMetric B} {gC : ConformalMetric C} {b : B} {c : C}

/-- Valid fixed-coordinate expressions are analytic by the universal
several-variable complex regularity theorem. -/
theorem coordinateFunction_analytic (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (a : UniformizingDiscChart gB b) (f : HolomorphicMap X B) (x : X)
    {z : ℂ × ℂ} (hz : Valid a f x z) :
    AnalyticAt ℂ (coordinateFunction a f x) z := by
  apply regularity
  have hi := (chartAt (ℂ × ℂ) x).continuousAt_symm hz.1
  have hf := f.holomorphic.continuous.continuousAt.comp hi
  have hsource := hf.tendsto (a.coordinates.open_source.mem_nhds hz.2)
  filter_upwards [hsource, (chartAt (ℂ × ℂ) x).open_target.mem_nhds hz.1]
    with q hq ht
  exact mdifferentiableAt_iff_differentiableAt.mp
    (coordinateFunction_mdifferentiableAt a f x ⟨ht, hq⟩)

/-- Joint surjectivity is preserved by the actual surface chart derivative
and the two actual uniformizing chart derivatives. -/
theorem pair_surjective_iff (a : UniformizingDiscChart gB b)
    (d : UniformizingDiscChart gC c) (f : HolomorphicMap X B) (g : HolomorphicMap X C)
    (x : X) {z : ℂ × ℂ} (hf : Valid a f x z) (hg : Valid d g x z) :
    Function.Surjective (fun v =>
      (fderiv ℂ (coordinateFunction a f x) z v,
        fderiv ℂ (coordinateFunction d g x) z v)) ↔
      Function.Surjective (fun v =>
        (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f ((chartAt (ℂ × ℂ) x).symm z) v,
          mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g ((chartAt (ℂ × ℂ) x).symm z) v)) := by
  let A : (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) :=
    (mdifferentiable_chart (I := 𝓘(ℂ, ℂ × ℂ)) x).symm.mfderiv hf.1
  let T : ℂ ≃L[ℂ] ℂ := a.mdifferentiable.mfderiv hf.2
  let S : ℂ ≃L[ℂ] ℂ := d.mdifferentiable.mfderiv hg.2
  rw [coordinateFunction_derivative a f x hf, coordinateFunction_derivative d g x hg]
  change Function.Surjective (fun v =>
    (T (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) f ((chartAt (ℂ × ℂ) x).symm z) (A v)),
      S (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g ((chartAt (ℂ × ℂ) x).symm z) (A v)))) ↔ _
  exact CoordinateCalculus.joint_surjective_iff _ _ A T S

end SurfaceCoordinates

section Normalization

variable {X : CompactComplexSurface} {D : Curve} {f g : Fibration X}
  {gB : ConformalMetric f.base} {gC : ConformalMetric g.base}

/-- At every valid normalization-coordinate point, insertion into the fixed
ambient coordinate expression recovers the actual restricted curve map as
a germ. The ambient chart may be fixed at any suitable source point. -/
theorem restricted_coordinate_comp_germ {b : f.base}
    (a : UniformizingDiscChart gB b) (ν : HolomorphicMap D X) (p : D) (x : X)
    {z : ℂ} (hz : z ∈ (chartAt ℂ p).target)
    (hν : ν ((chartAt ℂ p).symm z) ∈ (chartAt (ℂ × ℂ) x).source) :
    a.coordinateFunction (CoordinateCalculus.restrictedMap f ν) p =ᶠ[𝓝 z]
      coordinateFunction a (CoordinateCalculus.fibrationMap f) x ∘
        CoordinateCalculus.coordinateMap ν p x := by
  have hc := ν.holomorphic.continuous.continuousAt.comp ((chartAt ℂ p).continuousAt_symm hz)
  have hevent := hc.tendsto ((chartAt (ℂ × ℂ) x).open_source.mem_nhds hν)
  filter_upwards [hevent] with t ht
  change ν ((chartAt ℂ p).symm t) ∈ (chartAt (ℂ × ℂ) x).source at ht
  change a.coordinates (f (ν ((chartAt ℂ p).symm t))) =
    a.coordinates (f ((chartAt (ℂ × ℂ) x).symm
      ((chartAt (ℂ × ℂ) x) (ν ((chartAt ℂ p).symm t)))))
  rw [(chartAt (ℂ × ℂ) x).left_inv ht]

/-- The raw metric branch data are constructed from actual fibrations,
actual normalization, actual metric equality, and fixed target charts.
Every differential rank condition is transported through actual charts. -/
theorem metricBranchData_exists_spec
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts) (hf : f.Smooth) (hg : g.Smooth)
    (ν : HolomorphicMap D X) (p : D)
    (himage : ∀ q : D, ν q ∈ RamificationSupport.ramificationSet f g)
    (hu : Nonconstant (CoordinateCalculus.restrictedMap f ν))
    (hmetric : pullback (CoordinateCalculus.restrictedMap f ν) gB =
      pullback (CoordinateCalculus.restrictedMap g ν) gC)
    (a : UniformizingDiscChart gB (f (ν p)))
    (d : UniformizingDiscChart gC (g (ν p))) :
    ∃ A : MetricBranchData
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) (ν p))
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) (ν p))
      ((chartAt (ℂ × ℂ) (ν p)) (ν p)),
      A.normalization = CoordinateCalculus.coordinateMap ν p (ν p) ∧
        A.centre = (chartAt ℂ p) p := by
  let n := CoordinateCalculus.coordinateMap ν p (ν p)
  let c := (chartAt ℂ p) p
  let F := coordinateFunction a (CoordinateCalculus.fibrationMap f) (ν p)
  let G := coordinateFunction d (CoordinateCalculus.fibrationMap g) (ν p)
  have hnanalytic := CoordinateCalculus.curve_coordinateMap_analytic ν p
  have hnear : {z | z ∈ (chartAt ℂ p).target ∧
      ν ((chartAt ℂ p).symm z) ∈ (chartAt (ℂ × ℂ) (ν p)).source ∧
      f (ν ((chartAt ℂ p).symm z)) ∈ a.coordinates.source ∧
      g (ν ((chartAt ℂ p).symm z)) ∈ d.coordinates.source ∧
      AnalyticAt ℂ n z} ∈ 𝓝 c := by
    filter_upwards [CoordinateCalculus.coordinateMap_eventually_domains ν p,
      a.eventually_domains (CoordinateCalculus.restrictedMap f ν) p a.centre_mem,
      d.eventually_domains (CoordinateCalculus.restrictedMap g ν) p d.centre_mem,
      hnanalytic.eventually_analyticAt] with z hn ha hd hanz
    exact ⟨hn.1, hn.2, ha.2, hd.2, hanz⟩
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hnear
  let U := Metric.ball c r
  have hc : c ∈ U := Metric.mem_ball_self hr
  have hinv : ∀ z ∈ U, (chartAt (ℂ × ℂ) (ν p)).symm (n z) =
      ν ((chartAt ℂ p).symm z) := fun z hz =>
    (chartAt (ℂ × ℂ) (ν p)).left_inv (hball hz).2.1
  have hvalidF : ∀ z ∈ U,
      Valid a (CoordinateCalculus.fibrationMap f) (ν p) (n z) := by
    intro z hz
    refine ⟨(chartAt (ℂ × ℂ) (ν p)).map_source (hball hz).2.1, ?_⟩
    change f ((chartAt (ℂ × ℂ) (ν p)).symm (n z)) ∈ a.coordinates.source
    rw [hinv z hz]
    exact (hball hz).2.2.1
  have hvalidG : ∀ z ∈ U,
      Valid d (CoordinateCalculus.fibrationMap g) (ν p) (n z) := by
    intro z hz
    refine ⟨(chartAt (ℂ × ℂ) (ν p)).map_source (hball hz).2.1, ?_⟩
    change g ((chartAt (ℂ × ℂ) (ν p)).symm (n z)) ∈ d.coordinates.source
    rw [hinv z hz]
    exact (hball hz).2.2.2.1
  have hcompF : ∀ z ∈ U,
      a.coordinateFunction (CoordinateCalculus.restrictedMap f ν) p =ᶠ[𝓝 z] F ∘ n :=
    fun z hz => restricted_coordinate_comp_germ a ν p (ν p) (hball hz).1 (hball hz).2.1
  have hcompG : ∀ z ∈ U,
      d.coordinateFunction (CoordinateCalculus.restrictedMap g ν) p =ᶠ[𝓝 z] G ∘ n :=
    fun z hz => restricted_coordinate_comp_germ d ν p (ν p) (hball hz).1 (hball hz).2.1
  refine ⟨{ normalization := n
            centre := c
            centre_maps := CoordinateCalculus.coordinateMap_center ν p
            domain := U
            open_domain := Metric.isOpen_ball
            connected_domain := (convex_ball c r).isPreconnected
            centre_mem := hc
            normalization_analytic := fun z hz => (hball hz).2.2.2.2
            first_analytic := ?_
            second_analytic := ?_
            first_surjective := ?_
            second_surjective := ?_
            joint_not_surjective := ?_
            first_disc := fun z hz => coordinateFunction_disc a _ _ (hvalidF z hz)
            second_disc := fun z hz => coordinateFunction_disc d _ _ (hvalidG z hz)
            metric_identity := ?_
            derivative_order_finite := ?_ }, rfl, rfl⟩
  · exact fun z hz => coordinateFunction_analytic regularity a _ _ (hvalidF z hz)
  · exact fun z hz => coordinateFunction_analytic regularity d _ _ (hvalidG z hz)
  · intro z hz
    apply (coordinateFunction_surjective_iff a _ _ (hvalidF z hz)).mpr
    rw [hinv z hz]
    exact hf _
  · intro z hz
    apply (coordinateFunction_surjective_iff d _ _ (hvalidG z hz)).mpr
    rw [hinv z hz]
    exact hg _
  · intro z hz
    apply (pair_surjective_iff a d _ _ _ (hvalidF z hz) (hvalidG z hz)).not.mpr
    rw [hinv z hz]
    exact (CoordinateCalculus.pairMap_surjective_iff f g _).not.mp (himage _)
  · intro z hz
    have hF := hcompF z hz
    have hG := hcompG z hz
    have hden := a.pullback_density_eq d
      (CoordinateCalculus.restrictedMap f ν) (CoordinateCalculus.restrictedMap g ν) p
      hmetric (hball hz).1 (hball hz).2.2.1 (hball hz).2.2.2.1
    rw [hF.deriv_eq, hG.deriv_eq, hF.self_of_nhds, hG.self_of_nhds] at hden
    exact hden
  · intro htop
    apply a.coordinateFunction_derivative_order_finite maps
      (CoordinateCalculus.restrictedMap f ν) hu p a.centre_mem
    rw [analyticOrderAt_congr (hcompF c hc).deriv]
    exact htop

theorem metricBranchData_exists
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts) (hf : f.Smooth) (hg : g.Smooth)
    (ν : HolomorphicMap D X) (p : D)
    (himage : ∀ q : D, ν q ∈ RamificationSupport.ramificationSet f g)
    (hu : Nonconstant (CoordinateCalculus.restrictedMap f ν))
    (hmetric : pullback (CoordinateCalculus.restrictedMap f ν) gB =
      pullback (CoordinateCalculus.restrictedMap g ν) gC)
    (a : UniformizingDiscChart gB (f (ν p)))
    (d : UniformizingDiscChart gC (g (ν p))) :
    Nonempty (MetricBranchData
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) (ν p))
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) (ν p))
      ((chartAt (ℂ × ℂ) (ν p)) (ν p))) := by
  obtain ⟨A, _hν, _hc⟩ := metricBranchData_exists_spec regularity maps hf hg ν p himage hu hmetric a d
  exact ⟨A⟩

/-- A constructed branch retains its specified actual normalization and an
actual open domain of the full graph identity, for subsequent finite covers
of the actual critical set. -/
structure ConstructedBranch (F G : ℂ × ℂ → ℂ) (x : ℂ × ℂ)
    (ν : ℂ → ℂ × ℂ) (c : ℂ) where
  branch : BranchGraphs.NormalizedBranchGraph F G x
  normalization_eq : branch.normalization = ν
  centre_eq : branch.centre = c
  domain : Set ℂ
  open_domain : IsOpen domain
  connected_domain : IsPreconnected domain
  centre_mem : c ∈ domain
  graph_identity : ∀ z ∈ domain, G (ν z) = branch.graph (F (ν z))

theorem constructedBranch_exists
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (hf : f.Smooth) (hg : g.Smooth) (ν : HolomorphicMap D X) (p : D)
    (himage : ∀ q : D, ν q ∈ RamificationSupport.ramificationSet f g)
    (hu : Nonconstant (CoordinateCalculus.restrictedMap f ν))
    (hmetric : pullback (CoordinateCalculus.restrictedMap f ν) gB =
      pullback (CoordinateCalculus.restrictedMap g ν) gC)
    (a : UniformizingDiscChart gB (f (ν p)))
    (d : UniformizingDiscChart gC (g (ν p))) :
    Nonempty (ConstructedBranch
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) (ν p))
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) (ν p))
      ((chartAt (ℂ × ℂ) (ν p)) (ν p))
      (CoordinateCalculus.coordinateMap ν p (ν p)) ((chartAt ℂ p) p)) := by
  obtain ⟨A, hν, hc⟩ := metricBranchData_exists_spec regularity maps hf hg ν p himage hu hmetric a d
  obtain ⟨graph, hgraph⟩ := A.global_graph_exists extend
  refine ⟨{ branch := A.normalizedBranchGraph graph hgraph
            normalization_eq := hν
            centre_eq := hc
            domain := A.domain
            open_domain := A.open_domain
            connected_domain := A.connected_domain
            centre_mem := hc ▸ A.centre_mem
            graph_identity := ?_ }⟩
  intro z hz
  have h := hgraph z hz
  simpa only [hν, MetricBranchData.normalizedBranchGraph, MetricBranchData.localGraph] using h

/-- A normalized branch in fixed actual ambient and uniformizing target
coordinates. The graph, its regular inverse, and the accumulating regular
set are all constructed. -/
theorem normalizedBranchGraph_exists
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (hf : f.Smooth) (hg : g.Smooth) (ν : HolomorphicMap D X) (p : D)
    (himage : ∀ q : D, ν q ∈ RamificationSupport.ramificationSet f g)
    (hu : Nonconstant (CoordinateCalculus.restrictedMap f ν))
    (hmetric : pullback (CoordinateCalculus.restrictedMap f ν) gB =
      pullback (CoordinateCalculus.restrictedMap g ν) gC)
    (a : UniformizingDiscChart gB (f (ν p)))
    (d : UniformizingDiscChart gC (g (ν p))) :
    Nonempty (BranchGraphs.NormalizedBranchGraph
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) (ν p))
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) (ν p))
      ((chartAt (ℂ × ℂ) (ν p)) (ν p))) := by
  obtain ⟨A⟩ := metricBranchData_exists regularity maps hf hg ν p himage hu hmetric a d
  exact A.normalizedBranchGraph_exists extend

/-- The ambient source point can be fixed before the normalization branch.
Only the actual equality of its centre with that point is used to transport
the construction; the uniformizing charts are retained unchanged. -/
theorem constructedBranch_exists_fixed
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (hf : f.Smooth) (hg : g.Smooth) (x : X) (ν : HolomorphicMap D X) (p : D)
    (hcentre : ν p = x)
    (himage : ∀ q : D, ν q ∈ RamificationSupport.ramificationSet f g)
    (hu : Nonconstant (CoordinateCalculus.restrictedMap f ν))
    (hmetric : pullback (CoordinateCalculus.restrictedMap f ν) gB =
      pullback (CoordinateCalculus.restrictedMap g ν) gC)
    (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x)) :
    Nonempty (ConstructedBranch
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
      ((chartAt (ℂ × ℂ) x) x)
      (CoordinateCalculus.coordinateMap ν p x) ((chartAt ℂ p) p)) := by
  subst x
  exact constructedBranch_exists regularity maps extend hf hg ν p himage hu hmetric a d

/-- Any family of actual normalization branches at one source point is
constructed in the same two ambient functions. In particular this supports
a finite family without making separate target-coordinate choices. -/
theorem constructedBranch_family_exists {ι : Type*}
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (hf : f.Smooth) (hg : g.Smooth) (x : X)
    (sources : ι → Curve) (ν : ∀ i, HolomorphicMap (sources i) X)
    (p : ∀ i, sources i) (hcentre : ∀ i, ν i (p i) = x)
    (himage : ∀ i q, ν i q ∈ RamificationSupport.ramificationSet f g)
    (hu : ∀ i, Nonconstant (CoordinateCalculus.restrictedMap f (ν i)))
    (hmetric : ∀ i, pullback (CoordinateCalculus.restrictedMap f (ν i)) gB =
      pullback (CoordinateCalculus.restrictedMap g (ν i)) gC)
    (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x)) :
    Nonempty (∀ i, ConstructedBranch
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
      ((chartAt (ℂ × ℂ) x) x)
      (CoordinateCalculus.coordinateMap (ν i) (p i) x) ((chartAt ℂ (p i)) (p i))) := by
  exact ⟨fun i => Classical.choice (constructedBranch_exists_fixed regularity maps extend
    hf hg x (ν i) (p i) (hcentre i) (himage i) (hu i) (hmetric i) a d)⟩

/-- The proved global normalization comparison supplies the two analytic
inputs used by the fixed-coordinate branch construction. -/
theorem constructedBranch_of_comparison
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (constant : CovectorGauges.ClassicalZeroDifferentialConstancy)
    (pullbacks : ClassicalPullbackFacts) (unique : TroyanovUniqueness)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (hf : f.Smooth) (hg : g.Smooth) (hB : f.Hyperbolic)
    (ν : HolomorphicMap D X) (p : D)
    (himage : ∀ q : D, ν q ∈ RamificationSupport.ramificationSet f g)
    (hfinite : Fibration.FinitePair f g) (hν : ∃ q r : D, ν q ≠ ν r)
    (hBcone : HasConeData gB 0) (hCcone : HasConeData gC 0)
    (hBcurv : HasConstantCurvature gB 0 (-1))
    (hCcurv : HasConstantCurvature gC 0 (-1))
    (a : UniformizingDiscChart gB (f (ν p)))
    (d : UniformizingDiscChart gC (g (ν p))) :
    Nonempty (ConstructedBranch
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) (ν p))
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) (ν p))
      ((chartAt (ℂ × ℂ) (ν p)) (ν p))
      (CoordinateCalculus.coordinateMap ν p (ν p)) ((chartAt ℂ p) p)) := by
  obtain ⟨hu, _hv, _hD, _hR, _hDiv, hmetric⟩ :=
    CoordinateCalculus.normalized_comparison_complete regularity maps constant pullbacks unique
      f g hf hg hB ν himage hfinite hν gB gC hBcone hCcone hBcurv hCcurv
  exact constructedBranch_exists regularity maps extend hf hg ν p himage hu hmetric a d

end Normalization

/-- An actual normalization-image cover of the critical set, with the open
domains retained by the construction, gives the finite branch-cover record.
The graph identities come from the constructed branches, not from the cover
assumption. -/
def finiteBranchCover_of_constructed
    {F G : ℂ × ℂ → ℂ} {x : ℂ × ℂ} {ι : Type*} [Fintype ι]
    {ν : ι → ℂ → ℂ × ℂ} {c : ι → ℂ}
    (branches : ∀ i, ConstructedBranch F G x (ν i) (c i))
    (region : Set (ℂ × ℂ)) (hregion : IsOpen region) (hx : x ∈ region)
    (hcover : ∀ q ∈ region,
      ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) →
        ∃ i t, t ∈ (branches i).domain ∧ ν i t = q) :
    FiniteAnalyticGerm.FiniteBranchCover F G x ι where
  region := region
  open_region := hregion
  centre_mem := hx
  branches i := (branches i).branch
  branch_domain i := (branches i).domain
  critical_cover := by
    intro q hq hcritical
    obtain ⟨i, t, ht, hν⟩ := hcover q hq hcritical
    exact ⟨i, t, ht, by rw [(branches i).normalization_eq]; exact hν⟩
  branch_identity := by
    intro i t ht
    rw [(branches i).normalization_eq]
    exact (branches i).graph_identity t ht

end Paper27.Geometry.FixedAmbientBranchGraphs
