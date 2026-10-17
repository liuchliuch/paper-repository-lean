import Paper27.Geometry.FixedAmbientBranchGraphs
import Paper27.Geometry.EmbeddedCurve

/-!
# Unramified actual restrictions from uniformizing cyclic charts

The local cyclic classification is carried out in uniformizing target
coordinates. This file transports its differential conclusions back to the
actual restricted fibration maps. Neither unramifiedness nor immersion of a
normalization map is assumed; the inclusion here is an actual embedded curve.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry.UniformCyclicRestrictions

open FixedAmbientBranchGraphs NormalizedBranchConstruction
variable {X : CompactComplexSurface} {f g : Fibration X}
  {gB : MetricComparison.ConformalMetric f.base} {gC : MetricComparison.ConformalMetric g.base}

theorem restrictions_bijective (D : EmbeddedCurve X) (hD : D.TangentToPair f g)
    (p : D.curve) (a : UniformizingDiscChart gB (f (D.inclusion p)))
    (d : UniformizingDiscChart gC (g (D.inclusion p)))
    (B : CyclicModel.CyclicNormalForm
      (coordinateFunction a (CoordinateCalculus.fibrationMap f) (D.inclusion p))
      (coordinateFunction d (CoordinateCalculus.fibrationMap g) (D.inclusion p))
      ((chartAt (ℂ × ℂ) (D.inclusion p)) (D.inclusion p)))
    (hg : Function.Surjective
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g (D.inclusion p))) :
    Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p) ∧
      Function.Bijective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap g) p) := by
  let x := D.inclusion p
  let ν := CoordinateCalculus.coordinateMap D.inclusion p x
  let F := coordinateFunction a (CoordinateCalculus.fibrationMap f) x
  let G := coordinateFunction d (CoordinateCalculus.fibrationMap g) x
  let c := (chartAt ℂ p) p
  let z₀ := (chartAt (ℂ × ℂ) x) x
  have hν : AnalyticAt ℂ ν c := CoordinateCalculus.curve_coordinateMap_analytic D.inclusion p
  have hνc : ν c = z₀ := CoordinateCalculus.coordinateMap_center D.inclusion p
  have hnear : ∀ᶠ t in 𝓝 c, Valid a (CoordinateCalculus.fibrationMap f) x (ν t) ∧
      Valid d (CoordinateCalculus.fibrationMap g) x (ν t) := by
    have hcont : Tendsto ν (𝓝 c) (𝓝 z₀) := by
      simpa only [hνc] using hν.continuousAt.tendsto
    filter_upwards [hcont (valid_eventually a (CoordinateCalculus.fibrationMap f) x a.centre_mem),
      hcont (valid_eventually d (CoordinateCalculus.fibrationMap g) x d.centre_mem)] with t hf hg
    exact ⟨hf, hg⟩
  have hnot : ∀ᶠ t in 𝓝 c, ¬ Function.Surjective
      (fun v => (fderiv ℂ F (ν t) v, fderiv ℂ G (ν t) v)) := by
    filter_upwards [hnear, CoordinateCalculus.coordinateMap_eventually_domains D.inclusion p]
      with t ht hct
    apply (pair_surjective_iff a d (CoordinateCalculus.fibrationMap f)
      (CoordinateCalculus.fibrationMap g) x ht.1 ht.2).not.mpr
    have hcancel : (chartAt (ℂ × ℂ) x).symm (ν t) =
        D.inclusion ((chartAt ℂ p).symm t) :=
      (chartAt (ℂ × ℂ) x).left_inv hct.2
    rw [hcancel]
    exact (CoordinateCalculus.pairMap_surjective_iff f g _).not.mp
      (hD ⟨(chartAt ℂ p).symm t, rfl⟩)
  have hprod : ∀ q ∈ B.coordinate.chart.source,
      fderiv ℂ (fun z => (F z, G z)) q =
        (fderiv ℂ F q).prod (fderiv ℂ G q) := fun q hq =>
    (B.hasFDerivAt_first hq).differentiableAt.fderiv_prodMk
      (B.hasFDerivAt_second hq).differentiableAt
  have hpcrit : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) z₀) := by
    rw [hprod z₀ B.coordinate.source_mem]
    simpa only [hνc] using hnot.self_of_nhds
  have hsource : ∀ᶠ t in 𝓝 c, ν t ∈ B.coordinate.chart.source := by
    apply hν.continuousAt.tendsto
    rw [hνc]
    exact B.coordinate.chart.open_source.mem_nhds B.coordinate.source_mem
  have haxis : ∀ᶠ t in 𝓝 c, (B.coordinate.chart (ν t)).2 = 0 := by
    filter_upwards [hsource, hnot] with t ht hcrit
    apply (B.ramification_iff_normal_zero hpcrit ht).mp
    rw [hprod _ ht]
    exact hcrit
  have hG : Function.Surjective (fderiv ℂ G z₀) := by
    apply (coordinateFunction_surjective_iff d (CoordinateCalculus.fibrationMap g) x
      (by simpa only [hνc] using hnear.self_of_nhds.2)).mpr
    change Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) g
      ((chartAt (ℂ × ℂ) x).symm z₀))
    rw [show (chartAt (ℂ × ℂ) x).symm z₀ = x from
      (chartAt (ℂ × ℂ) x).left_inv (mem_chart_source (ℂ × ℂ) x)]
    exact hg
  let coord : CyclicModel.AnalyticCoordinateChart (ν c) :=
    { chart := B.coordinate.chart
      source_mem := hνc.symm ▸ B.coordinate.source_mem
      analytic := B.coordinate.analytic
      inverse_analytic := B.coordinate.inverse_analytic
      differential_bijective := B.coordinate.differential_bijective }
  let B' : CyclicModel.CyclicNormalForm F G (ν c) :=
    { coordinate := coord
      centre_x := B.centre_x
      centre_coordinates := by
        change B.coordinate.chart (ν c) = (B.centre_x, 0)
        rw [hνc]
        exact B.centre_coordinates
      exponent := B.exponent
      exponent_positive := B.exponent_positive
      graph := B.graph
      graph_analytic := B.graph_analytic
      identity := B.identity }
  have hbij := EmbeddedCurve.cyclic_restriction_differentials_bijective B'
    hν.differentiableAt (D.inclusion_coordinate_injective p) haxis
    (hνc.symm ▸ hpcrit) (hνc.symm ▸ hG)
  have hct : c ∈ (chartAt ℂ p).target :=
    (chartAt ℂ p).map_source (mem_chart_source ℂ p)
  have hcx : D.inclusion ((chartAt ℂ p).symm c) ∈ (chartAt (ℂ × ℂ) x).source := by
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact mem_chart_source (ℂ × ℂ) x
  have hfcomp := (restricted_coordinate_comp_germ a D.inclusion p x hct hcx).fderiv_eq (𝕜 := ℂ)
  have hgcomp := (restricted_coordinate_comp_germ d D.inclusion p x hct hcx).fderiv_eq (𝕜 := ℂ)
  have hfvalid : Valid a (D.restrictedMap f) p c := by
    refine ⟨hct, ?_⟩
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact a.centre_mem
  have hgvalid : Valid d (D.restrictedMap g) p c := by
    refine ⟨hct, ?_⟩
    rw [(chartAt ℂ p).left_inv (mem_chart_source ℂ p)]
    exact d.centre_mem
  have hfs : Function.Surjective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p) := by
    have hs := (coordinateFunction_surjective_iff a (D.restrictedMap f) p hfvalid).mp
      (by change Function.Surjective (fderiv ℂ (a.coordinateFunction
        (CoordinateCalculus.restrictedMap f D.inclusion) p) c); rw [hfcomp]; exact hbij.1.2)
    exact (show (chartAt ℂ p).symm c = p from
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)) ▸ hs
  have hgs : Function.Surjective (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap g) p) := by
    have hs := (coordinateFunction_surjective_iff d (D.restrictedMap g) p hgvalid).mp
      (by change Function.Surjective (fderiv ℂ (d.coordinateFunction
        (CoordinateCalculus.restrictedMap g D.inclusion) p) c); rw [hgcomp]; exact hbij.2.2)
    exact (show (chartAt ℂ p).symm c = p from
      (chartAt ℂ p).left_inv (mem_chart_source ℂ p)) ▸ hs
  let Lf : ℂ →ₗ[ℂ] ℂ := (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap f) p).toLinearMap
  let Lg : ℂ →ₗ[ℂ] ℂ := (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (D.restrictedMap g) p).toLinearMap
  have hfi : Function.Injective Lf := LinearMap.injective_iff_surjective.mpr hfs
  have hgi : Function.Injective Lg := LinearMap.injective_iff_surjective.mpr hgs
  exact ⟨⟨hfi, hfs⟩, ⟨hgi, hgs⟩⟩

end Paper27.Geometry.UniformCyclicRestrictions
