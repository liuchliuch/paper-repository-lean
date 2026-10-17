import Paper27.Geometry.RetractionCoefficientHolomorphic

/-!
# Deriving the third and difference orders from actual pair normal charts

Three actual pair atlases with the same exponent suffice for the scalar
orders used in the Appendix connection proof. No determinant multiplicity
or scalar order is supplied as a further geometric hypothesis. The key
ordinary calculus argument says that an invertible two-dimensional change
of coordinates has nonzero normal derivative on a slice whenever its first
component has zero derivative there.
-/
noncomputable section
open scoped Manifold Topology
open Filter
namespace Paper27.Geometry.ThreeRetractionOrders

open RetractionCoordinateGerms

variable {X : CompactComplexSurface}

def crossSlice (c d : OpenPartialHomeomorph X (ℂ × ℂ)) (a z : ℂ) : ℂ × ℂ :=
  d (c.symm (a, z))

theorem crossSlice_analytic (c d : OpenPartialHomeomorph X (ℂ × ℂ))
    (hc : c.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ))
    (hd : d.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ))
    (a : ℂ) (ht : (a, (0 : ℂ)) ∈ c.target) (hs : c.symm (a, (0 : ℂ)) ∈ d.source) :
    AnalyticAt ℂ (crossSlice c d a) 0 := by
  have hline : ContinuousAt (fun z : ℂ => (a, z)) 0 :=
    continuousAt_const.prodMk continuousAt_id
  have hct := hline.tendsto (c.open_target.mem_nhds ht)
  have hcs := (c.continuousAt_symm ht).comp hline
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [hct, hcs.tendsto (d.open_source.mem_nhds hs)] with z hz hdz
  have hlin : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun z : ℂ => (a, z)) z := mdifferentiableAt_iff_differentiableAt.mpr
    (differentiableAt_const a |>.prodMk differentiableAt_id)
  exact mdifferentiableAt_iff_differentiableAt.mp
    ((hd.mdifferentiableAt hdz).comp z ((hc.mdifferentiableAt_symm hz).comp z hlin))

/-- This is a calculation with actual invertible chart derivatives, not an
assumption that a chosen slice is transverse to the third map. -/
theorem crossSlice_normal_derivative_ne_zero (c d : OpenPartialHomeomorph X (ℂ × ℂ))
    (hc : c.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ))
    (hd : d.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ))
    (a : ℂ) (ht : (a, (0 : ℂ)) ∈ c.target) (hs : c.symm (a, (0 : ℂ)) ∈ d.source)
    (hfirst : deriv (fun z => (crossSlice c d a z).1) 0 = 0) :
    deriv (fun z => (crossSlice c d a z).2) 0 ≠ 0 := by
  let L : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
    (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) d (c.symm (a, (0 : ℂ)))).comp
      (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) c.symm (a, (0 : ℂ)))
  have hL : Function.Injective L :=
    (hd.mfderiv_injective hs).comp (hc.symm.mfderiv_injective ht)
  have hcomp := (hd.mdifferentiableAt hs).comp (a, (0 : ℂ)) (hc.mdifferentiableAt_symm ht)
  have heq : fderiv ℂ (d ∘ c.symm) (a, (0 : ℂ)) = L := by
    rw [← mfderiv_eq_fderiv, mfderiv_comp (a, (0 : ℂ))
      (hd.mdifferentiableAt hs) (hc.mdifferentiableAt_symm ht)]
  have hline : HasDerivAt (fun z : ℂ => (a, z)) (0, 1) 0 :=
    (hasDerivAt_const (0 : ℂ) a).prodMk (hasDerivAt_id (0 : ℂ))
  have h : HasDerivAt (crossSlice c d a) (L (0, 1)) 0 := by
    simpa only [heq] using
      (mdifferentiableAt_iff_differentiableAt.mp hcomp).hasFDerivAt.comp_hasDerivAt 0 hline
  have hfst' : HasDerivAt (fun z => (crossSlice c d a z).1) (L (0, 1)).1 0 :=
    (hasFDerivAt_fst (𝕜 := ℂ) (p := crossSlice c d a 0)).comp_hasDerivAt 0 h
  have hsnd' : HasDerivAt (fun z => (crossSlice c d a z).2) (L (0, 1)).2 0 :=
    (hasFDerivAt_snd (𝕜 := ℂ) (p := crossSlice c d a 0)).comp_hasDerivAt 0 h
  have hfst : (L (0, 1)).1 = 0 := hfst'.deriv.symm.trans hfirst
  intro hzero
  have hsnd : (L (0, 1)).2 = 0 := hsnd'.deriv.symm.trans hzero
  have hzero' : L (0, 1) = L (0, 0) :=
    (Prod.ext hfst hsnd).trans (map_zero L).symm
  have hv : ((0 : ℂ), (1 : ℂ)) = (0, 0) := hL hzero'
  exact (one_ne_zero : (1 : ℂ) ≠ 0) (congrArg Prod.snd hv)

theorem power_order_of_simple_zero {f : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hf0 : f 0 = 0) (hdf : deriv f 0 ≠ 0) (n : ℕ) :
    analyticOrderAt (fun z => f z ^ n) 0 = n := by
  have horder : analyticOrderAt f 0 = (1 : ℕ) :=
    order_eq_of_derivative_order (by omega) hf hf0
      (by simpa using analyticOrderAt_eq_zero.mpr (Or.inr hdf))
  change analyticOrderAt (f ^ n) 0 = n
  rw [analyticOrderAt_pow hf, horder]
  simp

variable {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}

end Paper27.Geometry.ThreeRetractionOrders

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open ThreeRetractionOrders RetractionCoefficientHolomorphic
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}

variable (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

theorem chart_mdifferentiable (i p : D.curve) :
    (A.chart i p).coordinates.MDifferentiable 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) :=
  ⟨A.holomorphic i p, A.inverse_holomorphic i p⟩

/-- Read the contact order of a second pair on the actual first pair's slice.
Only vanishing of the first derivative remains, and it is checked below for
each of the two relevant first retractions. -/
theorem cross_pair_contact_order {r s : D.Retraction U}
    (B : RetractionCoordinateGerms.NormalAtlas D U r s n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i)
    (hfirst : deriv (fun z =>
      ((B.chart i p).coordinates (A.slice i p z)).1) 0 = 0) :
    analyticOrderAt (fun z => A.coordinate s i p ((chartAt ℂ i) p, z) -
      A.coordinate r i p ((chartAt ℂ i) p, z)) 0 = n := by
  let c := (A.chart i p).coordinates
  let d := (B.chart i p).coordinates
  let a := (chartAt ℂ i) p
  have ht : (a, (0 : ℂ)) ∈ c.target := by
    rw [show (a, (0 : ℂ)) = c (D.inclusion p) from (A.centre i p hi).symm]
    exact c.map_source (A.source_mem i p hi)
  have hs : c.symm (a, (0 : ℂ)) ∈ d.source := by
    change A.slice i p 0 ∈ (B.chart i p).coordinates.source
    rw [A.slice_zero i p hi]
    exact B.source_mem i p hi
  have hN : AnalyticAt ℂ (fun z => (crossSlice c d a z).2) 0 :=
    analyticAt_snd.comp (crossSlice_analytic c d (A.chart_mdifferentiable i p)
      (B.chart_mdifferentiable i p) a ht hs)
  have hN0 : (crossSlice c d a 0).2 = 0 := by
    change ((B.chart i p).coordinates (A.slice i p 0)).2 = 0
    rw [A.slice_zero i p hi, B.centre i p hi]
  have hNd := crossSlice_normal_derivative_ne_zero c d
    (A.chart_mdifferentiable i p) (B.chart_mdifferentiable i p) a ht hs hfirst
  have horder := power_order_of_simple_zero hN hN0 hNd n
  have hmem : ∀ᶠ z in 𝓝 0, A.slice i p z ∈ (B.chart i p).coordinates.source :=
    A.slice_tendsto i p hi ((B.chart i p).coordinates.open_source.mem_nhds
      (B.source_mem i p hi))
  have heq : (fun z => A.coordinate s i p ((chartAt ℂ i) p, z) -
      A.coordinate r i p ((chartAt ℂ i) p, z)) =ᶠ[𝓝 0]
      fun z => (crossSlice c d a z).2 ^ n := by
    filter_upwards [hmem] with z hz
    change (chartAt ℂ i) (s.toFun (A.slice i p z)) -
      (chartAt ℂ i) (r.toFun (A.slice i p z)) = _
    rw [(B.chart i p).s_normal _ hz, (B.chart i p).r_normal _ hz]
    exact add_sub_cancel_left _ _
  exact (analyticOrderAt_congr heq).trans horder

theorem cross_first_retraction_derivative_zero
    (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₃ n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    deriv (fun z => ((B.chart i p).coordinates (A.slice i p z)).1) 0 = 0 := by
  have hmem := A.slice_tendsto i p hi ((B.chart i p).coordinates.open_source.mem_nhds
    (B.source_mem i p hi))
  have heq : (fun z => ((B.chart i p).coordinates (A.slice i p z)).1) =ᶠ[𝓝 0]
      fun _ => (chartAt ℂ i) p := by
    filter_upwards [hmem, A.slice_eventually i i p hi hi] with z hz hc
    have hcoord : (A.chart i p).coordinates (A.slice i p z) = ((chartAt ℂ i) p, z) :=
      (A.chart i p).coordinates.right_inv hc.1
    rw [← (B.chart i p).r_normal _ hz, (A.chart i p).r_normal _ hc.2.1,
      hcoord]
  simpa only [deriv_const] using heq.deriv_eq

/-- The exact order of the third retraction follows from the actual first/
third pair normal atlas. -/
theorem hasThirdOrder_of_pair_atlas
    (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₃ n) : A.HasThirdOrder r₃ := by
  intro i p hi
  have horder := A.cross_pair_contact_order B i p hi
    (A.cross_first_retraction_derivative_zero B i p hi)
  have heq : (fun z => A.coordinate r₃ i p ((chartAt ℂ i) p, z) -
      A.coordinate r₁ i p ((chartAt ℂ i) p, z)) =ᶠ[𝓝 0] A.third r₃ i p := by
    filter_upwards [A.slice_eventually i i p hi hi] with z hz
    have hcoord : (A.chart i p).coordinates (A.slice i p z) = ((chartAt ℂ i) p, z) :=
      (A.chart i p).coordinates.right_inv hz.1
    change (chartAt ℂ i) (r₃.toFun (A.slice i p z)) -
      (chartAt ℂ i) (r₁.toFun (A.slice i p z)) = _
    rw [(A.chart i p).r_normal _ hz.2.1, hcoord]
    rfl
  exact (analyticOrderAt_congr heq).symm.trans horder

theorem cross_second_retraction_derivative_zero
    (B : RetractionCoordinateGerms.NormalAtlas D U r₂ r₃ n) (hn : 2 ≤ n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    deriv (fun z => ((B.chart i p).coordinates (A.slice i p z)).1) 0 = 0 := by
  have hmem := A.slice_tendsto i p hi ((B.chart i p).coordinates.open_source.mem_nhds
    (B.source_mem i p hi))
  have heq : (fun z => ((B.chart i p).coordinates (A.slice i p z)).1) =ᶠ[𝓝 0]
      fun z => (chartAt ℂ i) p + z ^ n := by
    filter_upwards [hmem, A.slice_eventually i i p hi hi] with z hz hc
    have hcoord : (A.chart i p).coordinates (A.slice i p z) = ((chartAt ℂ i) p, z) :=
      (A.chart i p).coordinates.right_inv hc.1
    rw [← (B.chart i p).r_normal _ hz, (A.chart i p).s_normal _ hc.2.1,
      hcoord]
  have hp : HasDerivAt (fun z : ℂ => (chartAt ℂ i) p + z ^ n) 0 0 := by
    simpa only [zero_pow (by omega : n - 1 ≠ 0), mul_zero, add_zero] using
      (hasDerivAt_const 0 ((chartAt ℂ i) p)).add (hasDerivAt_pow n (0 : ℂ))
  exact heq.deriv_eq.trans hp.deriv

/-- The exact order of the difference follows from the actual second/third
pair normal atlas. The condition n≥2 makes the first component's derivative
on the first/second slice vanish. -/
theorem hasDifferenceOrder_of_pair_atlas
    (B : RetractionCoordinateGerms.NormalAtlas D U r₂ r₃ n) (hn : 2 ≤ n) :
    A.HasDifferenceOrder r₃ := by
  apply A.hasDifferenceOrder_of_coordinate_difference_order r₃
  intro i p hi
  exact A.cross_pair_contact_order B i p hi
    (A.cross_second_retraction_derivative_zero B hn i p hi)

include A
/-- The Appendix proof of Lemma 3.3 now consumes three actual pair atlases,
without either of the formerly separate scalar-order premises. -/
theorem common_tangency_impossible_of_three_pair_atlases
    (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₃ n)
    (C : RetractionCoordinateGerms.NormalAtlas D U r₂ r₃ n)
    (hn : 2 ≤ n) (T : TangentLineCocycle D.curve)
    (theory : LineBundleDegreeTheory) (hD : D.curve.Hyperbolic) : False :=
  A.common_tangency_impossible J P theory r₃ (A.hasThirdOrder_of_pair_atlas B)
    (A.hasDifferenceOrder_of_pair_atlas C hn) hn T hD

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
