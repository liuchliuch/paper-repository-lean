import Paper27.Geometry.FiniteBranchAssembly
import Paper27.Geometry.CoordinateFiniteGerms
import Paper27.Geometry.RamificationIndexConstancy

/-!
# Actual cyclic charts of the finite paired map

The actual finite pair is isolated in actual source and target charts.
The constructed finite family of normalized metric graphs supplies the
single smooth branch graph. General finite germ representatives and the
general finite-cover classification then give the actual Euclidean cyclic
model. Its source is restricted inside the valid original chart domains
before transporting it to the surface. The actual critical set is proved to
be the normal axis there, so these are genuine `SurfaceCyclicChart` data.
-/

noncomputable section

open scoped Manifold Topology

namespace Paper27.Geometry.ActualCyclicModels

open MetricComparison NormalizedBranchConstruction FixedAmbientBranchGraphs
  FiniteBranchAssembly CoordinateFiniteGerms RamificationIndexConstancy

variable {X : CompactComplexSurface} {f g : Fibration X}
  {gB : ConformalMetric f.base} {gC : ConformalMetric g.base}

/-- The actual product of the two fixed uniformizing target charts. -/
def targetChart (x : X) (a : UniformizingDiscChart gB (f x))
    (d : UniformizingDiscChart gC (g x)) :
    OpenPartialHomeomorph (f.base.productSurface g.base) (ℂ × ℂ) :=
  a.coordinates.prod d.coordinates

theorem targetChart_holomorphic (x : X) (a : UniformizingDiscChart gB (f x))
    (d : UniformizingDiscChart gC (g x)) :
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      (targetChart x a d) (targetChart x a d).source := by
  intro p hp
  have hfirst := (a.mdifferentiable.mdifferentiableAt hp.1).comp p
    ((f.base.firstProjection g.base).holomorphic p)
  have hsecond := (d.mdifferentiable.mdifferentiableAt hp.2).comp p
    ((f.base.secondProjection g.base).holomorphic p)
  exact (hfirst.prodMk_space hsecond).mdifferentiableWithinAt

theorem targetChart_inverse_holomorphic (x : X) (a : UniformizingDiscChart gB (f x))
    (d : UniformizingDiscChart gC (g x)) :
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
      (targetChart x a d).symm (targetChart x a d).target := by
  intro p hp
  have hfst : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (Prod.fst : ℂ × ℂ → ℂ) p :=
    mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_fst
  have hsnd : MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (Prod.snd : ℂ × ℂ → ℂ) p :=
    mdifferentiableAt_iff_differentiableAt.mpr differentiableAt_snd
  have hfirst := (a.mdifferentiable.mdifferentiableAt_symm hp.1).comp p hfst
  have hsecond := (d.mdifferentiable.mdifferentiableAt_symm hp.2).comp p hsnd
  simpa only [← modelWithCornersSelf_prod] using (hfirst.prodMk hsecond).mdifferentiableWithinAt

/-- Actual finite fibres give an isolated coordinate centre fibre, together
with a valid source neighbourhood for both fixed target coordinates. -/
theorem isolated_coordinate_pair
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (x : X) (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x)) :
    ∃ W : Set (ℂ × ℂ), IsOpen W ∧ (chartAt (ℂ × ℂ) x) x ∈ W ∧
      W ⊆ (chartAt (ℂ × ℂ) x).target ∧
      (∀ z ∈ W, Valid a (CoordinateCalculus.fibrationMap f) x z ∧
        Valid d (CoordinateCalculus.fibrationMap g) x z) ∧
      {z | z ∈ W ∧
        (coordinateFunction a (CoordinateCalculus.fibrationMap f) x z,
          coordinateFunction d (CoordinateCalculus.fibrationMap g) x z) =
        (coordinateFunction a (CoordinateCalculus.fibrationMap f) x ((chartAt (ℂ × ℂ) x) x),
          coordinateFunction d (CoordinateCalculus.fibrationMap g) x ((chartAt (ℂ × ℂ) x) x))} =
        {(chartAt (ℂ × ℂ) x) x} := by
  let q := RamificationSupport.finiteSurjectivePair f g hfinite hsurj
  obtain ⟨W, hW, hxW, htarget, hmaps, hfibre⟩ := isolated_coordinate_fibre
    q.map q.map.holomorphic.continuous q.finite_fibres
    (chartAt (ℂ × ℂ) x) (targetChart x a d) x (mem_chart_source (ℂ × ℂ) x)
    (show q.map x ∈ (targetChart x a d).source from ⟨a.centre_mem, d.centre_mem⟩)
  refine ⟨W, hW, hxW, htarget, ?_, hfibre⟩
  intro z hz
  exact ⟨⟨htarget hz, (hmaps z hz).1⟩, ⟨htarget hz, (hmaps z hz).2⟩⟩

/-- The actual paired critical condition is unchanged in the fixed ambient
chart and fixed uniformizing target charts. -/
theorem coordinate_critical_iff
    (x : X) (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x))
    {z : ℂ × ℂ} (ha : Valid a (CoordinateCalculus.fibrationMap f) x z)
    (hd : Valid d (CoordinateCalculus.fibrationMap g) x z) :
    ¬ Function.Surjective (fderiv ℂ (fun w =>
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x w,
        coordinateFunction d (CoordinateCalculus.fibrationMap g) x w)) z) ↔
      (chartAt (ℂ × ℂ) x).symm z ∈ RamificationSupport.ramificationSet f g := by
  have hF := mdifferentiableAt_iff_differentiableAt.mp
    (coordinateFunction_mdifferentiableAt a (CoordinateCalculus.fibrationMap f) x ha)
  have hG := mdifferentiableAt_iff_differentiableAt.mp
    (coordinateFunction_mdifferentiableAt d (CoordinateCalculus.fibrationMap g) x hd)
  rw [hF.fderiv_prodMk hG]
  exact ((pair_surjective_iff a d (CoordinateCalculus.fibrationMap f)
    (CoordinateCalculus.fibrationMap g) x ha hd).trans
      (CoordinateCalculus.pairMap_surjective_iff f g _).symm).not

/-- Restricting an actual cyclic model to an arbitrary smaller open source
preserves the actual maps, coordinate functions, graph, and exponent. -/
def restrictModel {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (B : CyclicModel.CyclicNormalForm F G p) (W : Set (ℂ × ℂ))
    (hW : IsOpen W) (hp : p ∈ W) : CyclicModel.CyclicNormalForm F G p where
  coordinate :=
    { chart := B.coordinate.chart.restrOpen W hW
      source_mem := ⟨B.coordinate.source_mem, hp⟩
      analytic := fun z hz => B.coordinate.analytic z hz.1
      inverse_analytic := fun z hz => B.coordinate.inverse_analytic z hz.1
      differential_bijective := fun z hz => B.coordinate.differential_bijective z hz.1 }
  centre_x := B.centre_x
  centre_coordinates := B.centre_coordinates
  exponent := B.exponent
  exponent_positive := B.exponent_positive
  graph := B.graph
  graph_analytic := fun z hz => B.graph_analytic z hz.1
  identity := fun z hz => B.identity z hz.1

theorem restrictModel_source_subset {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (B : CyclicModel.CyclicNormalForm F G p) (W : Set (ℂ × ℂ))
    (hW : IsOpen W) (hp : p ∈ W) :
    (restrictModel B W hW hp).coordinate.chart.source ⊆ W := Set.inter_subset_right

/-- The actual normalized branches, actual finite representative, and the
general cover classification construct a cyclic model at every actual
critical point. Its whole source is kept in the valid fixed chart domains. -/
theorem cyclic_model_exists
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (constant : CovectorGauges.ClassicalZeroDifferentialConstancy)
    (pullbacks : ClassicalPullbackFacts) (unique : TroyanovUniqueness)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (representatives : FiniteHolomorphicGermRepresentatives)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (classification : FiniteAnalyticGerm.SmoothBranchFiniteCoverClassification)
    (hf : f.Smooth) (hg : g.Smooth) (hB : f.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (hBcone : HasConeData gB 0) (hCcone : HasConeData gC 0)
    (hBcurv : HasConstantCurvature gB 0 (-1))
    (hCcurv : HasConstantCurvature gC 0 (-1))
    (x : X) (hx : x ∈ RamificationSupport.ramificationSet f g)
    (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x)) :
    ∃ B : CyclicModel.CyclicNormalForm
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
      ((chartAt (ℂ × ℂ) x) x),
      2 ≤ B.exponent ∧ ∀ z ∈ B.coordinate.chart.source,
        Valid a (CoordinateCalculus.fibrationMap f) x z ∧
          Valid d (CoordinateCalculus.fibrationMap g) x z := by
  obtain ⟨W, hW, hxW, _htarget, hvalid, hisolated⟩ :=
    isolated_coordinate_pair hfinite hsurj x a d
  have hvalidx := hvalid _ hxW
  have hF := coordinateFunction_analytic regularity a (CoordinateCalculus.fibrationMap f) x hvalidx.1
  have hG := coordinateFunction_analytic regularity d (CoordinateCalculus.fibrationMap g) x hvalidx.2
  have hsurjF := (coordinateFunction_surjective_iff a (CoordinateCalculus.fibrationMap f) x
    hvalidx.1).mpr (hf ((chartAt (ℂ × ℂ) x).symm ((chartAt (ℂ × ℂ) x) x)))
  obtain ⟨C⟩ := finiteBranchCover_exists regularity maps constant pullbacks unique extend hf hg hB
    hfinite hsurj N hBcone hCcone hBcurv hCcurv x a d
  obtain ⟨i₀⟩ := N.critical_has_branch x hx
  have hcrit : ¬ Function.Surjective (fderiv ℂ (fun z =>
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x z,
        coordinateFunction d (CoordinateCalculus.fibrationMap g) x z))
        ((chartAt (ℂ × ℂ) x) x)) := by
    apply (coordinate_critical_iff x a d hvalidx.1 hvalidx.2).mpr
    rwa [(chartAt (ℂ × ℂ) x).left_inv (mem_chart_source (ℂ × ℂ) x)]
  obtain ⟨B, _hgraph, hn⟩ := ramified_cyclic_model_of_branch_cover representatives rigidity
    classification C hF hG hsurjF i₀ ⟨W, hW, hxW, hisolated⟩ hcrit
  exact ⟨restrictModel B W hW hxW, hn,
    fun z hz => hvalid z ((restrictModel_source_subset B W hW hxW) hz)⟩

def modelChartMDifferentiable {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ}
    (B : CyclicModel.CyclicNormalForm F G p) :
    B.coordinate.chart.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) := by
  constructor
  · intro z hz
    exact (mdifferentiableAt_iff_differentiableAt.mpr
      (B.coordinate.analytic z hz).differentiableAt).mdifferentiableWithinAt
  · intro z hz
    exact (mdifferentiableAt_iff_differentiableAt.mpr
      (B.coordinate.inverse_analytic z hz).differentiableAt).mdifferentiableWithinAt

/-- An actual Euclidean cyclic model on the valid original coordinate
domains transports to an actual surface cyclic chart. In particular, the
critical-axis equality is deduced from the actual differential calculation. -/
def surfaceChartOfModel
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (x : X) (hx : x ∈ RamificationSupport.ramificationSet f g)
    (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x))
    (B : CyclicModel.CyclicNormalForm
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x)
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) x)
      ((chartAt (ℂ × ℂ) x) x)) (hn : 2 ≤ B.exponent)
    (hvalid : ∀ z ∈ B.coordinate.chart.source,
      Valid a (CoordinateCalculus.fibrationMap f) x z ∧
        Valid d (CoordinateCalculus.fibrationMap g) x z) :
    SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) x := by
  let e := chartAt (ℂ × ℂ) x
  have hmd := (mdifferentiable_chart (I := 𝓘(ℂ, ℂ × ℂ)) x).trans (modelChartMDifferentiable B)
  have hcrit : ¬ Function.Surjective (fderiv ℂ (fun z =>
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) x z,
        coordinateFunction d (CoordinateCalculus.fibrationMap g) x z)) (e x)) := by
    apply (coordinate_critical_iff x a d
      (hvalid _ B.coordinate.source_mem).1 (hvalid _ B.coordinate.source_mem).2).mpr
    rwa [e.left_inv (mem_chart_source (ℂ × ℂ) x)]
  refine
    { source := e.trans B.coordinate.chart
      target := targetChart x a d
      source_mem := ⟨mem_chart_source (ℂ × ℂ) x, B.coordinate.source_mem⟩
      source_holomorphic := hmd.1
      source_inverse_holomorphic := hmd.2
      target_holomorphic := targetChart_holomorphic x a d
      target_inverse_holomorphic := targetChart_inverse_holomorphic x a d
      maps_target := ?_
      exponent := B.exponent
      exponent_ge_two := hn
      graph := B.graph
      graph_analytic := ?_
      identity := ?_
      axis := ?_ }
  · intro q hq
    have hv := hvalid (e q) hq.2
    change f q ∈ a.coordinates.source ∧ g q ∈ d.coordinates.source
    have hfa : f (e.symm (e q)) ∈ a.coordinates.source := hv.1.2
    have hgd : g (e.symm (e q)) ∈ d.coordinates.source := hv.2.2
    rw [e.left_inv hq.1] at hfa hgd
    exact ⟨hfa, hgd⟩
  · intro q hq
    exact B.graph_analytic (e q) hq.2
  · intro q hq
    have hid := B.identity (e q) hq.2
    change (a.coordinates (f (e.symm (e q))), d.coordinates (g (e.symm (e q)))) = _ at hid
    rw [e.left_inv hq.1] at hid
    exact hid
  · intro q hq
    change q ∈ RamificationSupport.ramificationSet f g ↔ (B.coordinate.chart (e q)).2 = 0
    have hv := hvalid (e q) hq.2
    have hc := coordinate_critical_iff x a d hv.1 hv.2
    rw [e.left_inv hq.1] at hc
    exact hc.symm.trans (B.ramification_iff_normal_zero hcrit hq.2)

/-- Every actual critical point of the finite pair admits an actual surface
cyclic chart. The only classical inputs are the separately stated universal
normalization, metric, finite-germ, and finite-cover theorems. -/
theorem surface_cyclic_chart_exists
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (maps : ClassicalCurveMapFacts)
    (constant : CovectorGauges.ClassicalZeroDifferentialConstancy)
    (pullbacks : ClassicalPullbackFacts) (unique : TroyanovUniqueness)
    (extend : DiscGraphExtension.LocalDiscIsometryExtension)
    (representatives : FiniteHolomorphicGermRepresentatives)
    (rigidity : BranchGraphs.IsometryFirstJetRigidity)
    (classification : FiniteAnalyticGerm.SmoothBranchFiniteCoverClassification)
    (hf : f.Smooth) (hg : g.Smooth) (hB : f.Hyperbolic)
    (hfinite : f.FinitePair g) (hsurj : f.PairSurjective g)
    (N : CriticalCurveNormalization (RamificationSupport.finiteSurjectivePair f g hfinite hsurj))
    (hBcone : HasConeData gB 0) (hCcone : HasConeData gC 0)
    (hBcurv : HasConstantCurvature gB 0 (-1))
    (hCcurv : HasConstantCurvature gC 0 (-1))
    (x : X) (hx : x ∈ RamificationSupport.ramificationSet f g)
    (a : UniformizingDiscChart gB (f x)) (d : UniformizingDiscChart gC (g x)) :
    Nonempty (SurfaceCyclicChart (RamificationSupport.finiteSurjectivePair f g hfinite hsurj) x) := by
  obtain ⟨B, hn, hvalid⟩ := cyclic_model_exists regularity maps constant pullbacks unique extend
    representatives rigidity classification hf hg hB hfinite hsurj N hBcone hCcone hBcurv hCcurv x hx a d
  exact ⟨surfaceChartOfModel hfinite hsurj x hx a d B hn hvalid⟩

end Paper27.Geometry.ActualCyclicModels
