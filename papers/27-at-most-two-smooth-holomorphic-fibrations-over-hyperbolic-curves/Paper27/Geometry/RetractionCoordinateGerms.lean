import Paper27.Geometry.EmbeddedCurve
import Paper27.Geometry.TaylorGerms
import Mathlib.Analysis.Analytic.Order

/-!
# Retraction coordinate germs from actual normal charts

The normal chart is chosen separately for every pair `(i,p)`. Both functional
compatibility identities are proved from actual chart inverse identities and
three actual retractions. The scalar order of the third retraction is an
explicit geometric multiplicity input; it does not follow from arbitrary
retractions. Its analytic unit factor is constructed by mathlib's ordinary
analytic order theorem. No compatible jets or connection are assumed.
-/

noncomputable section
open scoped Manifold Topology
open Filter Polynomial

namespace Paper27.Geometry.RetractionCoordinateGerms

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}

/-- Actual local biholomorphic normal charts, indexed by both the base chart
and the point. Conditions at the centre are required only in the base domain. -/
structure NormalAtlas (D : EmbeddedCurve X) (U : D.Neighbourhood)
    (r₁ r₂ : D.Retraction U) (n : ℕ) where
  chart : ∀ (i _p : D.curve),
    RetractionAtlas.NormalFormChart D.curve r₁.toFun r₂.toFun n i
  source_mem : ∀ i p, p ∈ D.curve.chartDomain i →
    D.inclusion p ∈ (chart i p).coordinates.source
  centre : ∀ i p, p ∈ D.curve.chartDomain i →
    (chart i p).coordinates (D.inclusion p) = ((chartAt ℂ i) p, 0)
  source_subset : ∀ i p, (chart i p).coordinates.source ⊆ U.domain
  holomorphic : ∀ i p, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    (chart i p).coordinates (chart i p).coordinates.source
  inverse_holomorphic : ∀ i p, MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    (chart i p).coordinates.symm (chart i p).coordinates.target

/-- A continuous factor of a fixed monomial is determined at the centre. -/
theorem monomial_factor_at_zero {f g : ℂ → ℂ} (m : ℕ)
    (hf : ContinuousAt f 0) (hg : ContinuousAt g 0)
    (h : (fun z => z ^ m * f z) =ᶠ[𝓝 0] fun z => z ^ m * g z) : f 0 = g 0 := by
  apply tendsto_nhds_unique_of_eventuallyEq (l := 𝓝[≠] (0 : ℂ))
    hf.continuousWithinAt hg.continuousWithinAt
  filter_upwards [h.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with z hz hne
  exact mul_left_cancel₀ (pow_ne_zero m (show z ≠ 0 from hne)) hz

 theorem zero_dslope_factor (f : ℂ → ℂ) (hf : f 0 = 0) (z : ℂ) :
    f z = z * dslope f 0 z := by
  simpa only [sub_zero, smul_eq_mul, hf] using (sub_smul_dslope f 0 z).symm

/-- A finite order for the derivative recovers the order of an analytic
function vanishing at the centre. This is an ordinary scalar calculus lemma. -/
theorem order_eq_of_derivative_order {f : ℂ → ℂ} {m : ℕ} (hm : 0 < m)
    (hf : AnalyticAt ℂ f 0) (hf0 : f 0 = 0)
    (hd : analyticOrderAt (deriv f) 0 = (m - 1 : ℕ)) :
    analyticOrderAt f 0 = m := by
  have hfinite : analyticOrderAt f 0 ≠ ⊤ := by
    intro htop
    have hz : f =ᶠ[𝓝 0] (fun _ : ℂ => (0 : ℂ)) := analyticOrderAt_eq_top.mp htop
    have hdz : ∀ᶠ z in 𝓝 (0 : ℂ), deriv f z = 0 := by
      filter_upwards [hz.deriv] with z hzz
      simpa only [deriv_const] using hzz
    have hdt := analyticOrderAt_eq_top.mpr hdz
    rw [hd] at hdt
    exact (ENat.coe_ne_top _) hdt
  obtain ⟨g, hg, hg0, hfactor⟩ := hf.analyticOrderAt_ne_top.mp hfinite
  let k := analyticOrderNatAt f 0
  have hfg : f =ᶠ[𝓝 0] fun z => z ^ k * g z := by
    simpa only [sub_zero, smul_eq_mul] using hfactor
  have hk : 0 < k := by
    by_contra hnot
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hnot
    have hcentre := hfg.self_of_nhds
    simp only [hk0, pow_zero, one_mul, hf0] at hcentre
    exact hg0 hcentre.symm
  let h : ℂ → ℂ := fun z => (k : ℂ) * g z + z * deriv g z
  have hh : AnalyticAt ℂ h 0 :=
    (analyticAt_const.mul hg).add (analyticAt_id.mul hg.deriv)
  have hh0 : h 0 ≠ 0 := by
    change (k : ℂ) * g 0 + 0 * deriv g 0 ≠ 0
    simp only [zero_mul, add_zero]
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hk)) hg0
  have hdf : deriv f =ᶠ[𝓝 0] fun z => z ^ (k - 1) * h z := by
    filter_upwards [hfg.deriv, hg.eventually_analyticAt] with z hz hgz
    have hp := ((hasDerivAt_pow k z).mul hgz.differentiableAt.hasDerivAt).deriv
    have hpower : z ^ k = z ^ (k - 1) * z := by
      conv_lhs => rw [show k = (k - 1) + 1 by omega]
      exact pow_succ z (k - 1)
    calc
      deriv f z = (k : ℂ) * z ^ (k - 1) * g z + z ^ k * deriv g z := hz.trans hp
      _ = z ^ (k - 1) * h z := by dsimp only [h]; rw [hpower]; ring
  have hdk : analyticOrderAt (deriv f) 0 = (k - 1 : ℕ) :=
    hf.deriv.analyticOrderAt_eq_natCast.mpr
      ⟨h, hh, hh0, by simpa only [sub_zero, smul_eq_mul] using hdf⟩
  have hpred : k - 1 = m - 1 := by exact_mod_cast hdk.symm.trans hd
  have hkm : k = m := by omega
  rw [← Nat.cast_analyticOrderNatAt hfinite]
  exact congrArg (fun j : ℕ => (j : ℕ∞)) hkm

namespace NormalAtlas

variable (A : NormalAtlas D U r₁ r₂ n)

/-- The actual normal slice of the chart chosen at `(i,p)`. -/
def slice (i p : D.curve) (z : ℂ) : X :=
  (A.chart i p).coordinates.symm ((chartAt ℂ i) p, z)

def third (r₃ : D.Retraction U) (i p : D.curve) (z : ℂ) : ℂ :=
  (chartAt ℂ i) (r₃.toFun (A.slice i p z)) - (chartAt ℂ i) p

def normal (i j p : D.curve) (z : ℂ) : ℂ :=
  ((A.chart j p).coordinates (A.slice i p z)).2

/-- The actual written coordinate of a retraction in the chosen normal chart. -/
def coordinate (r : D.Retraction U) (i p : D.curve) (w : ℂ × ℂ) : ℂ :=
  (chartAt ℂ i) (r.toFun ((A.chart i p).coordinates.symm w))

/-- The determinant of the two actual coordinate differentials. -/
def pairDeterminant (r s : D.Retraction U) (i p : D.curve) (w : ℂ × ℂ) : ℂ :=
  fderiv ℂ (A.coordinate r i p) w (1, 0) * fderiv ℂ (A.coordinate s i p) w (0, 1) -
    fderiv ℂ (A.coordinate r i p) w (0, 1) * fderiv ℂ (A.coordinate s i p) w (1, 0)

 theorem coordinate_mdifferentiableAt (r : D.Retraction U) (i p : D.curve)
    {w : ℂ × ℂ} (hw : w ∈ (A.chart i p).coordinates.target)
    (hb : r.toFun ((A.chart i p).coordinates.symm w) ∈ D.curve.chartDomain i) :
    MDifferentiableAt 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ) (A.coordinate r i p) w := by
  have hinv := (A.inverse_holomorphic i p).mdifferentiableAt
    ((A.chart i p).coordinates.open_target.mem_nhds hw)
  have hr := r.holomorphic.mdifferentiableAt (U.open_domain.mem_nhds
    (A.source_subset i p ((A.chart i p).coordinates.map_target hw)))
  exact ((mdifferentiable_chart i).mdifferentiableAt hb).comp w (hr.comp w hinv)

 theorem coordinate_first_germ (i p : D.curve) {w : ℂ × ℂ}
    (hw : w ∈ (A.chart i p).coordinates.target) :
    A.coordinate r₁ i p =ᶠ[𝓝 w] Prod.fst := by
  filter_upwards [(A.chart i p).coordinates.open_target.mem_nhds hw] with v hv
  change (chartAt ℂ i) (r₁.toFun ((A.chart i p).coordinates.symm v)) = v.1
  rw [(A.chart i p).r_normal _ ((A.chart i p).coordinates.map_target hv),
    (A.chart i p).coordinates.right_inv hv]

 theorem pairDeterminant_first (r : D.Retraction U) (i p : D.curve) {w : ℂ × ℂ}
    (hw : w ∈ (A.chart i p).coordinates.target) :
    A.pairDeterminant r₁ r i p w = fderiv ℂ (A.coordinate r i p) w (0, 1) := by
  have hf := (A.coordinate_first_germ i p hw).fderiv_eq (𝕜 := ℂ)
  unfold pairDeterminant
  rw [hf, fderiv_fst]
  change (1 : ℂ) * _ - 0 * _ = _
  simp only [one_mul, zero_mul, sub_zero]

 theorem slice_zero (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.slice i p 0 = D.inclusion p := by
  rw [slice, ← A.centre i p hi]
  exact (A.chart i p).coordinates.left_inv (A.source_mem i p hi)

 theorem slice_tendsto (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    Tendsto (A.slice i p) (𝓝 0) (𝓝 (D.inclusion p)) := by
  have ht : ((chartAt ℂ i) p, (0 : ℂ)) ∈ (A.chart i p).coordinates.target := by
    rw [← A.centre i p hi]
    exact (A.chart i p).coordinates.map_source (A.source_mem i p hi)
  have hc := ((A.chart i p).coordinates.continuousAt_symm ht).comp
    (continuousAt_const.prodMk continuousAt_id)
  have h := hc.tendsto
  change Tendsto (A.slice i p) (𝓝 0) (𝓝 (A.slice i p 0)) at h
  rwa [A.slice_zero i p hi] at h

 theorem slice_eventually (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    ∀ᶠ z in 𝓝 0, ((chartAt ℂ i) p, z) ∈ (A.chart i p).coordinates.target ∧
      A.slice i p z ∈ (A.chart i p).coordinates.source ∧
      A.slice i p z ∈ (A.chart j p).coordinates.source := by
  have ht : ((chartAt ℂ i) p, (0 : ℂ)) ∈ (A.chart i p).coordinates.target := by
    rw [← A.centre i p hi]
    exact (A.chart i p).coordinates.map_source (A.source_mem i p hi)
  have hline : Tendsto (fun z : ℂ => ((chartAt ℂ i) p, z)) (𝓝 0)
      (𝓝 ((chartAt ℂ i) p, (0 : ℂ))) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  filter_upwards [hline ((A.chart i p).coordinates.open_target.mem_nhds ht),
    A.slice_tendsto i p hi ((A.chart j p).coordinates.open_source.mem_nhds
      (A.source_mem j p hj))] with z hz hjz
  exact ⟨hz, (A.chart i p).coordinates.map_target hz, hjz⟩

 theorem normal_zero (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    A.normal i j p 0 = 0 := by
  simp only [normal, A.slice_zero i p hi, A.centre j p hj]

 theorem third_zero (r₃ : D.Retraction U) (i p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) : A.third r₃ i p 0 = 0 := by
  simp only [third, A.slice_zero i p hi, r₃.retract, sub_self]

 theorem normal_analytic (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    AnalyticAt ℂ (A.normal i j p) 0 := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [A.slice_eventually i j p hi hj] with z hz
  have hline : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun z : ℂ => ((chartAt ℂ i) p, z)) z :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (differentiableAt_const ((chartAt ℂ i) p) |>.prodMk differentiableAt_id)
  have hinv := (A.inverse_holomorphic i p).mdifferentiableAt
    ((A.chart i p).coordinates.open_target.mem_nhds hz.1)
  have hchart := (A.holomorphic j p).mdifferentiableAt
    ((A.chart j p).coordinates.open_source.mem_nhds hz.2.2)
  exact (mdifferentiableAt_iff_differentiableAt.mp
    (hchart.comp z (hinv.comp z hline))).snd

 theorem third_analytic (r₃ : D.Retraction U) (i p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) : AnalyticAt ℂ (A.third r₃ i p) 0 := by
  have hr : Tendsto (fun z => r₃.toFun (A.slice i p z)) (𝓝 0) (𝓝 p) := by
    have hc := (r₃.holomorphic.mdifferentiableAt
      (U.open_domain.mem_nhds (U.contains p))).continuousAt.tendsto
    simpa only [r₃.retract] using hc.comp (A.slice_tendsto i p hi)
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [A.slice_eventually i i p hi hi,
    hr ((chartAt ℂ i).open_source.mem_nhds hi)] with z hz hb
  have hline : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun z : ℂ => ((chartAt ℂ i) p, z)) z :=
    mdifferentiableAt_iff_differentiableAt.mpr
      (differentiableAt_const ((chartAt ℂ i) p) |>.prodMk differentiableAt_id)
  have hinv := (A.inverse_holomorphic i p).mdifferentiableAt
    ((A.chart i p).coordinates.open_target.mem_nhds hz.1)
  have hr₃ := r₃.holomorphic.mdifferentiableAt
    (U.open_domain.mem_nhds (A.source_subset i p hz.2.1))
  exact (mdifferentiableAt_iff_differentiableAt.mp
    (((mdifferentiable_chart i).mdifferentiableAt hb).comp z
      (hr₃.comp z (hinv.comp z hline)))).sub_const _

/-- The inverse normal slice is reconstructed from the actual first retraction. -/
 theorem slice_normal_germ (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    (fun z => A.slice j p (A.normal i j p z)) =ᶠ[𝓝 0] A.slice i p := by
  filter_upwards [A.slice_eventually i j p hi hj] with z hz
  have hcoord : (A.chart i p).coordinates (A.slice i p z) = ((chartAt ℂ i) p, z) :=
    (A.chart i p).coordinates.right_inv hz.1
  have hfirst := (RetractionAtlas.overlap_formula_three D.curve r₁.toFun r₂.toFun n i j
    (A.chart i p) (A.chart j p) (A.slice i p z) hz.2.1 hz.2.2).1
  rw [hcoord, RetractionAtlas.chartChange_at_point D.curve i j p hi] at hfirst
  have heq : ((chartAt ℂ j) p, A.normal i j p z) =
      (A.chart j p).coordinates (A.slice i p z) :=
    Prod.ext hfirst.symm rfl
  change (A.chart j p).coordinates.symm _ = _
  rw [heq]
  exact (A.chart j p).coordinates.left_inv hz.2.2

 theorem normal_inverse_germ (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    A.normal j i p ∘ A.normal i j p =ᶠ[𝓝 0] id := by
  filter_upwards [A.slice_normal_germ i j p hi hj, A.slice_eventually i j p hi hj] with z hz hc
  change ((A.chart i p).coordinates (A.slice j p (A.normal i j p z))).2 = z
  rw [hz]
  exact congrArg Prod.snd ((A.chart i p).coordinates.right_inv hc.1)

 theorem normal_derivative_ne_zero (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    deriv (A.normal i j p) 0 ≠ 0 := by
  have hderiv := (A.normal_inverse_germ i j p hi hj).deriv_eq
  rw [deriv_comp 0 (by simpa only [A.normal_zero i j p hi hj] using
      (A.normal_analytic j i p hj hi).differentiableAt)
    (A.normal_analytic i j p hi hj).differentiableAt, deriv_id] at hderiv
  intro hz
  rw [hz, mul_zero] at hderiv
  exact zero_ne_one hderiv

/-- Formula (3) on the actual normal slice, proved without a germ assumption. -/
 theorem normal_identity (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    (fun z => A.normal i j p z ^ n) =ᶠ[𝓝 0]
      TaylorGerms.baseChange D.curve i j p ∘ (fun z => z ^ n) := by
  filter_upwards [A.slice_eventually i j p hi hj] with z hz
  have h := (RetractionAtlas.overlap_formula_three D.curve r₁.toFun r₂.toFun n i j
    (A.chart i p) (A.chart j p) (A.slice i p z) hz.2.1 hz.2.2).2
  have hcoord : (A.chart i p).coordinates (A.slice i p z) = ((chartAt ℂ i) p, z) :=
    (A.chart i p).coordinates.right_inv hz.1
  rw [hcoord] at h
  exact h

/-- The same third actual map in two charts gives its exact composition law. -/
 theorem third_identity (r₃ : D.Retraction U) (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    A.third r₃ j p ∘ A.normal i j p =ᶠ[𝓝 0]
      TaylorGerms.baseChange D.curve i j p ∘ A.third r₃ i p := by
  have hr : Tendsto (fun z => r₃.toFun (A.slice i p z)) (𝓝 0) (𝓝 p) := by
    have hc := (r₃.holomorphic.mdifferentiableAt
      (U.open_domain.mem_nhds (U.contains p))).continuousAt.tendsto
    simpa only [r₃.retract] using hc.comp (A.slice_tendsto i p hi)
  filter_upwards [A.slice_normal_germ i j p hi hj,
    hr ((chartAt ℂ i).open_source.mem_nhds hi)] with z hz hb
  change (chartAt ℂ j) (r₃.toFun (A.slice j p (A.normal i j p z))) - (chartAt ℂ j) p =
    D.curve.chartChange i j ((chartAt ℂ i) p +
      ((chartAt ℂ i) (r₃.toFun (A.slice i p z)) - (chartAt ℂ i) p)) -
        D.curve.chartChange i j ((chartAt ℂ i) p)
  rw [hz, add_sub_cancel, RetractionAtlas.chartChange_at_point D.curve i j _ hb,
    RetractionAtlas.chartChange_at_point D.curve i j p hi]

/-- Ordinary analytic order supplies the factor; this is not geometric input. -/
 theorem third_unit_factor (r₃ : D.Retraction U) (i p : D.curve)
    (hi : p ∈ D.curve.chartDomain i)
    (horder : analyticOrderAt (A.third r₃ i p) 0 = n) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h 0 ∧ h 0 ≠ 0 ∧
      A.third r₃ i p =ᶠ[𝓝 0] fun z => z ^ n * h z := by
  simpa only [sub_zero, smul_eq_mul] using
    ((A.third_analytic r₃ i p hi).analyticOrderAt_eq_natCast.mp horder)

/-- The raw multiplicity is kept separate from the normal chart data. -/
def HasThirdOrder (r₃ : D.Retraction U) : Prop :=
  ∀ i p, p ∈ D.curve.chartDomain i → analyticOrderAt (A.third r₃ i p) 0 = n

/-- Along the actual normal slice, the actual paired determinant is the
ordinary derivative of the third coordinate function. -/
 theorem pairDeterminant_derivative_germ (r₃ : D.Retraction U) (i p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) :
    (fun z => A.pairDeterminant r₁ r₃ i p ((chartAt ℂ i) p, z)) =ᶠ[𝓝 0]
      deriv (A.third r₃ i p) := by
  have hr : Tendsto (fun z => r₃.toFun (A.slice i p z)) (𝓝 0) (𝓝 p) := by
    have hc := (r₃.holomorphic.mdifferentiableAt
      (U.open_domain.mem_nhds (U.contains p))).continuousAt.tendsto
    simpa only [r₃.retract] using hc.comp (A.slice_tendsto i p hi)
  filter_upwards [A.slice_eventually i i p hi hi,
    hr ((chartAt ℂ i).open_source.mem_nhds hi)] with z hz hb
  have hG := mdifferentiableAt_iff_differentiableAt.mp
    (A.coordinate_mdifferentiableAt r₃ i p hz.1 hb)
  have hline : HasDerivAt (fun t : ℂ => ((chartAt ℂ i) p, t)) (0, 1) z :=
    (hasDerivAt_const z ((chartAt ℂ i) p)).prodMk (hasDerivAt_id z)
  have hchain : HasDerivAt (A.third r₃ i p)
      (fderiv ℂ (A.coordinate r₃ i p) ((chartAt ℂ i) p, z) (0, 1)) z :=
    (hG.hasFDerivAt.comp_hasDerivAt z hline).sub_const ((chartAt ℂ i) p)
  exact (A.pairDeterminant_first r₃ i p hz.1).trans hchain.deriv.symm

/-- In normal coordinates `r₁=x`, the paired determinant is the normal
partial derivative of the third coordinate function. Its finite order suffices
for `HasThirdOrder`; no scalar factor is supplied. -/
 theorem hasThirdOrder_of_derivative_order (r₃ : D.Retraction U) (hn : 0 < n)
    (hd : ∀ i p, p ∈ D.curve.chartDomain i →
      analyticOrderAt (deriv (A.third r₃ i p)) 0 = (n - 1 : ℕ)) :
    A.HasThirdOrder r₃ := by
  intro i p hi
  exact order_eq_of_derivative_order hn (A.third_analytic r₃ i p hi)
    (A.third_zero r₃ i p hi) (hd i p hi)

/-- The geometric input can be stated directly as finite order of the actual
coordinate pair determinant, rather than as order of an auxiliary factor. -/
 theorem hasThirdOrder_of_pairDeterminant_order (r₃ : D.Retraction U) (hn : 0 < n)
    (hd : ∀ i p, p ∈ D.curve.chartDomain i →
      analyticOrderAt
        (fun z => A.pairDeterminant r₁ r₃ i p ((chartAt ℂ i) p, z)) 0 = (n - 1 : ℕ)) :
    A.HasThirdOrder r₃ := by
  apply A.hasThirdOrder_of_derivative_order r₃ hn
  intro i p hi
  exact (analyticOrderAt_congr (A.pairDeterminant_derivative_germ r₃ i p hi)).symm.trans
    (hd i p hi)

 def thirdFactor (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃)
    (i p : D.curve) : ℂ → ℂ := by
  classical
  exact if hi : p ∈ D.curve.chartDomain i then
    Classical.choose (A.third_unit_factor r₃ i p hi (ho i p hi)) else 0

 theorem thirdFactor_spec (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    AnalyticAt ℂ (A.thirdFactor r₃ ho i p) 0 ∧ A.thirdFactor r₃ ho i p 0 ≠ 0 ∧
      A.third r₃ i p =ᶠ[𝓝 0] fun z => z ^ n * A.thirdFactor r₃ ho i p z := by
  classical
  unfold thirdFactor
  rw [dif_pos hi]
  exact Classical.choose_spec (A.third_unit_factor r₃ i p hi (ho i p hi))

/-- The leading coefficient may initially vary with both choices `(i,p)`. -/
def leading (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (i p : D.curve) : ℂ :=
  A.thirdFactor r₃ ho i p 0

 theorem leading_ne_zero (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) : A.leading r₃ ho i p ≠ 0 :=
  (A.thirdFactor_spec r₃ ho i p hi).2.1

/-- Exact order of the actual third-minus-second slice rules out leading
coefficient one. This remains a scalar multiplicity condition on actual maps. -/
 theorem leading_ne_one_of_difference_order (r₃ : D.Retraction U)
    (ho : A.HasThirdOrder r₃) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i)
    (hd : analyticOrderAt (fun z => A.third r₃ i p z - z ^ n) 0 = n) :
    A.leading r₃ ho i p ≠ 1 := by
  have hf : AnalyticAt ℂ (fun z => A.third r₃ i p z - z ^ n) 0 :=
    (A.third_analytic r₃ i p hi).sub (analyticAt_id.pow n)
  obtain ⟨g, hg, hg0, hfg⟩ := hf.analyticOrderAt_eq_natCast.mp hd
  have hraw : (fun z => z ^ n * (A.thirdFactor r₃ ho i p z - 1)) =ᶠ[𝓝 0]
      fun z => z ^ n * g z := by
    filter_upwards [(A.thirdFactor_spec r₃ ho i p hi).2.2, hfg] with z hz hgz
    simp only [sub_zero, smul_eq_mul] at hgz
    rw [hz] at hgz
    convert hgz using 1 <;> ring
  have hc : ContinuousAt (fun z => A.thirdFactor r₃ ho i p z - 1) 0 :=
    ((A.thirdFactor_spec r₃ ho i p hi).1.continuousAt).sub continuousAt_const
  have hh := monomial_factor_at_zero n hc hg.continuousAt hraw
  intro hone
  change A.thirdFactor r₃ ho i p 0 = 1 at hone
  rw [hone, sub_self] at hh
  exact hg0 hh.symm

/-- The normal derivative has the actual tangent transition as its nth power.
Only continuity of ordinary divided differences is needed here. -/
 theorem normal_power_leading (hn : 0 < n) (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    deriv (A.normal i j p) 0 ^ n = D.curve.chartJacobian i j p := by
  let N := A.normal i j p
  let B := TaylorGerms.baseChange D.curve i j p
  have hN : N 0 = 0 := A.normal_zero i j p hi hj
  have hB : B 0 = 0 := TaylorGerms.baseChange_zero D.curve i j p
  have hcN : ContinuousAt (dslope N 0) 0 :=
    continuousAt_dslope_same.mpr (A.normal_analytic i j p hi hj).differentiableAt
  have hcB : ContinuousAt (dslope B 0) 0 := continuousAt_dslope_same.mpr
    (TaylorGerms.baseChange_analytic D.curve i j p hi hj).differentiableAt
  have hpow : ContinuousAt (fun z : ℂ => z ^ n) 0 := continuousAt_id.pow n
  have hcB' : ContinuousAt (dslope B 0) ((fun z : ℂ => z ^ n) 0) := by
    simpa only [zero_pow (Nat.ne_of_gt hn)] using hcB
  have hc : ContinuousAt (fun z : ℂ => dslope B 0 (z ^ n)) 0 := hcB'.comp (f := fun z : ℂ => z ^ n) hpow
  have hraw : (fun z => z ^ n * dslope N 0 z ^ n) =ᶠ[𝓝 0]
      fun z => z ^ n * dslope B 0 (z ^ n) := by
    filter_upwards [A.normal_identity i j p hi hj] with z hz
    change N z ^ n = B (z ^ n) at hz
    rw [zero_dslope_factor N hN z, mul_pow, zero_dslope_factor B hB (z ^ n)] at hz
    exact hz
  have hh := monomial_factor_at_zero n (hcN.pow n) hc hraw
  simp only [dslope_same, zero_pow (Nat.ne_of_gt hn)] at hh
  exact hh.trans (TaylorGerms.baseChange_first D.curve i j p)

/-- Before global constancy, the leading coefficient already obeys its raw
transition law, obtained from the two proved functional identities. -/
 theorem leading_transition (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃)
    (hn : 0 < n) (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    A.leading r₃ ho j p * D.curve.chartJacobian i j p =
      D.curve.chartJacobian i j p * A.leading r₃ ho i p := by
  let N := A.normal i j p
  let B := TaylorGerms.baseChange D.curve i j p
  let fi := A.thirdFactor r₃ ho i p
  let fj := A.thirdFactor r₃ ho j p
  have hN : N 0 = 0 := A.normal_zero i j p hi hj
  have hB : B 0 = 0 := TaylorGerms.baseChange_zero D.curve i j p
  have hcN : ContinuousAt N 0 := (A.normal_analytic i j p hi hj).continuousAt
  have htN : Tendsto N (𝓝 0) (𝓝 0) := by simpa only [hN] using hcN.tendsto
  have hcB : ContinuousAt (dslope B 0) 0 := continuousAt_dslope_same.mpr
    (TaylorGerms.baseChange_analytic D.curve i j p hi hj).differentiableAt
  have hcD : ContinuousAt (dslope N 0) 0 := continuousAt_dslope_same.mpr
    (A.normal_analytic i j p hi hj).differentiableAt
  have hci := (A.thirdFactor_spec r₃ ho i p hi).1.continuousAt
  have hcj := (A.thirdFactor_spec r₃ ho j p hj).1.continuousAt
  have hct := (A.third_analytic r₃ i p hi).continuousAt
  have hcj' : ContinuousAt fj (N 0) := by simpa only [hN] using hcj
  have hcB' : ContinuousAt (dslope B 0) (A.third r₃ i p 0) := by
    simpa only [A.third_zero r₃ i p hi] using hcB
  have hleft : ContinuousAt (fun z => dslope N 0 z ^ n * fj (N z)) 0 :=
    (hcD.pow n).mul (hcj'.comp hcN)
  have hright : ContinuousAt (fun z => fi z * dslope B 0 (A.third r₃ i p z)) 0 :=
    hci.mul (hcB'.comp hct)
  have hraw : (fun z => z ^ n * (dslope N 0 z ^ n * fj (N z))) =ᶠ[𝓝 0]
      fun z => z ^ n * (fi z * dslope B 0 (A.third r₃ i p z)) := by
    filter_upwards [A.third_identity r₃ i j p hi hj,
      htN ((A.thirdFactor_spec r₃ ho j p hj).2.2),
      (A.thirdFactor_spec r₃ ho i p hi).2.2] with z hz hjz hiz
    change A.third r₃ j p (N z) = B (A.third r₃ i p z) at hz
    change A.third r₃ j p (N z) = N z ^ n * fj (N z) at hjz
    change A.third r₃ i p z = z ^ n * fi z at hiz
    have hh : N z ^ n * fj (N z) =
        z ^ n * fi z * dslope B 0 (A.third r₃ i p z) := by
      calc
        _ = B (A.third r₃ i p z) := hjz.symm.trans hz
        _ = A.third r₃ i p z * dslope B 0 (A.third r₃ i p z) :=
          zero_dslope_factor B hB _
        _ = _ := congrArg (fun w => w * dslope B 0 (A.third r₃ i p z)) hiz
    nth_rw 1 [zero_dslope_factor N hN z] at hh
    simpa only [mul_pow, mul_assoc] using hh
  have hh := monomial_factor_at_zero n hleft hright hraw
  have hh' : deriv N 0 ^ n * A.leading r₃ ho j p =
      A.leading r₃ ho i p * D.curve.chartJacobian i j p := by
    simpa only [dslope_same, hN, A.third_zero r₃ i p hi,
      B, fi, fj, TaylorGerms.baseChange_first, leading] using hh
  rw [A.normal_power_leading hn i j p hi hj] at hh'
  calc
    A.leading r₃ ho j p * D.curve.chartJacobian i j p =
        D.curve.chartJacobian i j p * A.leading r₃ ho j p := mul_comm _ _
    _ = A.leading r₃ ho i p * D.curve.chartJacobian i j p := hh'
    _ = D.curve.chartJacobian i j p * A.leading r₃ ho i p := mul_comm _ _

 theorem leading_overlap (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃)
    (hn : 0 < n) (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    A.leading r₃ ho j p = A.leading r₃ ho i p := by
  have hp : D.curve.chartJacobian i j p ≠ 0 := by
    rw [← A.normal_power_leading hn i j p hi hj]
    exact pow_ne_zero n (A.normal_derivative_ne_zero i j p hi hj)
  apply mul_right_cancel₀ hp
  simpa only [mul_comm (D.curve.chartJacobian i j p)] using
    A.leading_transition r₃ ho hn i j p hi hj

/-- Once coefficient gluing proves a global constant, all the raw analytic
fields of `RetractionGerms` are constructed from the actual maps and charts. -/
def toRetractionGerms (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃)
    (T : TangentLineCocycle D.curve) (a : ℂ)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a) :
    TaylorGerms.RetractionGerms D.curve T n a where
  third := A.third r₃
  thirdFactor := A.thirdFactor r₃ ho
  normal := A.normal
  third_analytic := A.third_analytic r₃
  factor_analytic i p hi := (A.thirdFactor_spec r₃ ho i p hi).1
  factor_leading := ha
  third_factor i p hi := (A.thirdFactor_spec r₃ ho i p hi).2.2
  normal_analytic := A.normal_analytic
  normal_zero := A.normal_zero
  normal_derivative_ne_zero := A.normal_derivative_ne_zero
  normal_identity := A.normal_identity
  third_identity := A.third_identity r₃

/-- The finite compatible jets required by Appendix A now come from the
actual retractions, the actual chart family, and the universal Taylor functor. -/
def compatibleJets (J : TaylorGerms.TaylorCalculus) (r₃ : D.Retraction U)
    (ho : A.HasThirdOrder r₃) (T : TangentLineCocycle D.curve) (a : ℂ)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a) (hn : 2 ≤ n) :
    CompatibleRetractionJets D.curve T n a
      ((A.toRetractionGerms r₃ ho T a ha).doubleCoefficient J) :=
  (A.toRetractionGerms r₃ ho T a ha).compatibleJets J hn

 theorem equation_seven_of_actual_retractions (J : TaylorGerms.TaylorCalculus)
    (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃)
    (T : TangentLineCocycle D.curve) (a : ℂ)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a) (hn : 2 ≤ n)
    (i j p : D.curve) (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    (A.toRetractionGerms r₃ ho T a ha).doubleCoefficient J j p *
        D.curve.chartJacobian i j p ^ 2 =
      D.curve.chartJacobian i j p * (A.toRetractionGerms r₃ ho T a ha).doubleCoefficient J i p +
        (a ^ 2 - a) / 2 * D.curve.coordinateDerivative i (T.bundle.transition i j) p :=
  (A.toRetractionGerms r₃ ho T a ha).equation_seven_from_germs J hn i j p hi hj

end NormalAtlas
end Paper27.Geometry.RetractionCoordinateGerms
