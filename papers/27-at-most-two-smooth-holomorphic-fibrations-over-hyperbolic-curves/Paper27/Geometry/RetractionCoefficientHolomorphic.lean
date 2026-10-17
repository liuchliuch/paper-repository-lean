import Paper27.Geometry.RetractionCoordinateGerms
import Paper27.Geometry.CoefficientGluing
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Holomorphic coefficients independent of normal chart choices

The only additional classical interface below concerns ordinary Taylor
coefficients of arbitrary analytic functions of two complex variables.
Normal rotations, independence of the chosen normal charts, the holomorphic
local coefficient functions, compact constancy, and the resulting connection
are proved for the actual retractions.
-/
noncomputable section
open scoped Manifold Topology
open Filter Polynomial

namespace Paper27.Geometry.RetractionCoefficientHolomorphic
open RetractionCoordinateGerms

/-- The ordinary several-variable analytic and parameter-Taylor theorem. The
functions and open domains are arbitrary; there are no geometric coefficients,
retractions, or connections in this interface. The classical source is Lebl,
*Tasty Bits of Several Complex Variables*, v4.4, Theorem 1.2.1 (power-series
representation on a polydisc), together with the ordinary coefficient formula. -/
structure ParametricTaylorCalculus (J : TaylorGerms.TaylorCalculus) : Prop where
  regularity : CoordinateCalculus.SurfaceAnalyticRegularity
  parameter : ∀ (d k : ℕ) (F : ℂ × ℂ → ℂ) (V : Set (ℂ × ℂ)), IsOpen V →
    AnalyticOnNhd ℂ F V → ∀ x : ℂ, (x, 0) ∈ V →
      AnalyticAt ℂ (fun t => (J.jet d (fun z => F (t, z))).coeff k) x

namespace ParametricTaylorCalculus
 theorem parameter_at {J : TaylorGerms.TaylorCalculus} (P : ParametricTaylorCalculus J)
    (d k : ℕ) (F : ℂ × ℂ → ℂ) (x : ℂ) (hF : AnalyticAt ℂ F (x, 0)) :
    AnalyticAt ℂ (fun t => (J.jet d (fun z => F (t, z))).coeff k) x := by
  obtain ⟨V, hV, hopen, hx⟩ := eventually_nhds_iff.mp hF.eventually_analyticAt
  exact P.parameter d k F V hopen hV x hx
end ParametricTaylorCalculus

/-- A differentiable normal germ with unchanged nth power is a rotation germ.
Finite root values and continuity force the quotient to be locally constant. -/
theorem rotation_germ {N : ℂ → ℂ} {n : ℕ} (hn : 0 < n)
    (hN : DifferentiableAt ℂ N 0) (hzero : N 0 = 0)
    (hpower : (fun z => N z ^ n) =ᶠ[𝓝 0] fun z => z ^ n) :
    deriv N 0 ^ n = 1 ∧ N =ᶠ[𝓝 0] fun z => deriv N 0 * z := by
  let q := dslope N 0
  have hq : ContinuousAt q 0 := continuousAt_dslope_same.mpr hN
  have hraw : (fun z => z ^ n * q z ^ n) =ᶠ[𝓝 0] fun z => z ^ n * (1 : ℂ) := by
    filter_upwards [hpower] with z hz
    rw [zero_dslope_factor N hzero z, mul_pow] at hz
    exact hz.trans (mul_one _).symm
  have hq0 : q 0 ^ n = 1 := monomial_factor_at_zero n (hq.pow n) continuousAt_const hraw
  have hroot : ∀ᶠ z in 𝓝 0, q z ^ n = 1 := by
    filter_upwards [hraw] with z hz
    by_cases h : z = 0
    · simpa only [h] using hq0
    · exact mul_left_cancel₀ (pow_ne_zero n h) hz
  let S : Set ℂ := {z | z ^ n = 1}
  have hS : S.Finite := by
    apply (Polynomial.nthRootsFinset n (1 : ℂ)).finite_toSet.subset
    intro z hz
    exact (Polynomial.mem_nthRootsFinset hn 1).mpr hz
  have he : IsOpen (S \ {q 0})ᶜ := (hS.diff : (S \ {q 0}).Finite).isClosed.isOpen_compl
  have hnear : ∀ᶠ z in 𝓝 0, q z ∉ S \ {q 0} :=
    hq (he.mem_nhds (by simp))
  have heq : q =ᶠ[𝓝 0] fun _ => q 0 := by
    filter_upwards [hroot, hnear] with z hz hnot
    by_contra hne
    exact hnot ⟨hz, hne⟩
  refine ⟨by simpa only [q, dslope_same] using hq0, ?_⟩
  filter_upwards [heq] with z hz
  rw [zero_dslope_factor N hzero z]
  change z * q z = deriv N 0 * z
  rw [hz, show q 0 = deriv N 0 from dslope_same N 0, mul_comm]

/-- Rotation preserves every coefficient whose degree is a multiple of n. -/
theorem coefficient_rotation (J : TaylorGerms.TaylorCalculus)
    {f g N : ℂ → ℂ} {n d k : ℕ} (hn : 0 < n) (hd : 1 ≤ d) (hk : k ≤ d) (hkd : n ∣ k)
    (_hf : AnalyticAt ℂ f 0) (hg : AnalyticAt ℂ g 0) (hN : AnalyticAt ℂ N 0)
    (hzero : N 0 = 0) (hpower : (fun z => N z ^ n) =ᶠ[𝓝 0] fun z => z ^ n)
    (hcomp : g ∘ N =ᶠ[𝓝 0] f) : (J.jet d g).coeff k = (J.jet d f).coeff k := by
  obtain ⟨hroot, hrotation⟩ := rotation_germ hn hN.differentiableAt hzero hpower
  have hlinear : J.jet d N = C (deriv N 0) * X := by
    rw [J.congr d hrotation]
    have hp := J.polynomial d (C (deriv N 0) * X) (by
      exact (natDegree_mul_le.trans (by simpa using hd)))
    simpa only [eval_mul, eval_C, eval_X] using hp
  have hc := (J.composition d g N hg hN hzero).coefficient k hk
  rw [J.congr d hcomp, hlinear, comp_C_mul_X_coeff] at hc
  obtain ⟨m, rfl⟩ := hkd
  have hpow : deriv N 0 ^ (n * m) = 1 := by rw [pow_mul, hroot, one_pow]
  rw [hpow, mul_one] at hc
  exact hc.symm

variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}

/-- A single actual normal chart valid at a specified centre. -/
structure CenteredChart (D : EmbeddedCurve X) (U : D.Neighbourhood)
    (r₁ r₂ : D.Retraction U) (n : ℕ) (i p : D.curve) where
  chart : RetractionAtlas.NormalFormChart D.curve r₁.toFun r₂.toFun n i
  source_mem : D.inclusion p ∈ chart.coordinates.source
  centre : chart.coordinates (D.inclusion p) = ((chartAt ℂ i) p, 0)
  source_subset : chart.coordinates.source ⊆ U.domain
  holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    chart.coordinates chart.coordinates.source
  inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    chart.coordinates.symm chart.coordinates.target

namespace CenteredChart
variable {i p : D.curve} (c e : CenteredChart D U r₁ r₂ n i p)

def slice (z : ℂ) : X := c.chart.coordinates.symm ((chartAt ℂ i) p, z)
def third (r₃ : D.Retraction U) (z : ℂ) : ℂ :=
  (chartAt ℂ i) (r₃.toFun (c.slice z)) - (chartAt ℂ i) p
def normal (z : ℂ) : ℂ := (e.chart.coordinates (c.slice z)).2

 theorem slice_zero : c.slice 0 = D.inclusion p := by
  rw [slice, ← c.centre]
  exact c.chart.coordinates.left_inv c.source_mem

 theorem slice_tendsto : Tendsto c.slice (𝓝 0) (𝓝 (D.inclusion p)) := by
  have ht : ((chartAt ℂ i) p, (0 : ℂ)) ∈ c.chart.coordinates.target := by
    rw [← c.centre]
    exact c.chart.coordinates.map_source c.source_mem
  have hc := (c.chart.coordinates.continuousAt_symm ht).comp
    (continuousAt_const.prodMk continuousAt_id)
  have h := hc.tendsto
  change Tendsto c.slice (𝓝 0) (𝓝 (c.slice 0)) at h
  rwa [c.slice_zero] at h

 theorem eventually_domains : ∀ᶠ z in 𝓝 0,
    ((chartAt ℂ i) p, z) ∈ c.chart.coordinates.target ∧
      c.slice z ∈ c.chart.coordinates.source ∧ c.slice z ∈ e.chart.coordinates.source := by
  have ht : ((chartAt ℂ i) p, (0 : ℂ)) ∈ c.chart.coordinates.target := by
    rw [← c.centre]
    exact c.chart.coordinates.map_source c.source_mem
  have hline : Tendsto (fun z : ℂ => ((chartAt ℂ i) p, z)) (𝓝 0)
      (𝓝 ((chartAt ℂ i) p, (0 : ℂ))) :=
    (continuousAt_const.prodMk continuousAt_id).tendsto
  filter_upwards [hline (c.chart.coordinates.open_target.mem_nhds ht),
    c.slice_tendsto (e.chart.coordinates.open_source.mem_nhds e.source_mem)] with z hz he
  exact ⟨hz, c.chart.coordinates.map_target hz, he⟩

 theorem normal_analytic : AnalyticAt ℂ (c.normal e) 0 := by
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [c.eventually_domains e] with z hz
  have hline : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun z : ℂ => ((chartAt ℂ i) p, z)) z :=
    mdifferentiableAt_iff_differentiableAt.mpr
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have hinv := c.inverse_holomorphic.mdifferentiableAt
    (c.chart.coordinates.open_target.mem_nhds hz.1)
  have he := e.holomorphic.mdifferentiableAt
    (e.chart.coordinates.open_source.mem_nhds hz.2.2)
  exact (mdifferentiableAt_iff_differentiableAt.mp (he.comp z (hinv.comp z hline))).snd

 theorem normal_zero : c.normal e 0 = 0 := by
  simp only [normal, c.slice_zero, e.centre]

 theorem third_analytic (r₃ : D.Retraction U) (hi : p ∈ D.curve.chartDomain i) :
    AnalyticAt ℂ (c.third r₃) 0 := by
  have hr : Tendsto (fun z => r₃.toFun (c.slice z)) (𝓝 0) (𝓝 p) := by
    have hc := (r₃.holomorphic.mdifferentiableAt
      (U.open_domain.mem_nhds (U.contains p))).continuousAt.tendsto
    simpa only [r₃.retract] using hc.comp c.slice_tendsto
  apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
  filter_upwards [c.eventually_domains c, hr ((chartAt ℂ i).open_source.mem_nhds hi)] with z hz hb
  have hline : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ × ℂ)
      (fun z : ℂ => ((chartAt ℂ i) p, z)) z :=
    mdifferentiableAt_iff_differentiableAt.mpr
      ((differentiableAt_const _).prodMk differentiableAt_id)
  have hinv := c.inverse_holomorphic.mdifferentiableAt
    (c.chart.coordinates.open_target.mem_nhds hz.1)
  have hr₃ := r₃.holomorphic.mdifferentiableAt
    (U.open_domain.mem_nhds (c.source_subset hz.2.1))
  exact (mdifferentiableAt_iff_differentiableAt.mp
    (((mdifferentiable_chart i).mdifferentiableAt hb).comp z
      (hr₃.comp z (hinv.comp z hline)))).sub_const _

 theorem comparison_germs :
    ((fun z => c.normal e z ^ n) =ᶠ[𝓝 0] fun z => z ^ n) ∧
      (fun z => e.slice (c.normal e z)) =ᶠ[𝓝 0] c.slice := by
  have hall : ∀ᶠ z in 𝓝 0, c.normal e z ^ n = z ^ n ∧
      e.slice (c.normal e z) = c.slice z := by
    filter_upwards [c.eventually_domains e] with z hz
    have hc : c.chart.coordinates (c.slice z) = ((chartAt ℂ i) p, z) :=
      c.chart.coordinates.right_inv hz.1
    have hfirst : (e.chart.coordinates (c.slice z)).1 = (chartAt ℂ i) p := by
      rw [← e.chart.r_normal _ hz.2.2, c.chart.r_normal _ hz.2.1, hc]
    have hpower : c.normal e z ^ n = z ^ n := by
      have he := e.chart.s_normal _ hz.2.2
      rw [c.chart.s_normal _ hz.2.1, hc, hfirst] at he
      change (chartAt ℂ i) p + z ^ n = (chartAt ℂ i) p + c.normal e z ^ n at he
      exact (add_left_cancel he).symm
    refine ⟨hpower, ?_⟩
    have heq : ((chartAt ℂ i) p, c.normal e z) = e.chart.coordinates (c.slice z) :=
      Prod.ext hfirst.symm rfl
    change e.chart.coordinates.symm _ = _
    rw [heq]
    exact e.chart.coordinates.left_inv hz.2.2
  exact ⟨hall.mono fun _ h => h.1, hall.mono fun _ h => h.2⟩

 theorem third_comparison (r₃ : D.Retraction U) :
    e.third r₃ ∘ c.normal e =ᶠ[𝓝 0] c.third r₃ := by
  filter_upwards [(c.comparison_germs e).2] with z hz
  change (chartAt ℂ i) (r₃.toFun (e.slice (c.normal e z))) - (chartAt ℂ i) p = _
  rw [hz]
  rfl

 theorem coefficient_independent (J : TaylorGerms.TaylorCalculus) (r₃ : D.Retraction U)
    (hn : 0 < n) (hi : p ∈ D.curve.chartDomain i) (d k : ℕ)
    (hd : 1 ≤ d) (hk : k ≤ d) (hkd : n ∣ k) :
    (J.jet d (e.third r₃)).coeff k = (J.jet d (c.third r₃)).coeff k := by
  exact coefficient_rotation J hn hd hk hkd (c.third_analytic r₃ hi) (e.third_analytic r₃ hi)
    (c.normal_analytic e) (c.normal_zero e) (c.comparison_germs e).1 (c.third_comparison e r₃)

/-- Every point of the embedded curve in this fixed chart has zero normal
coordinate, by the two actual retraction identities. -/
 theorem centre_at (q : D.curve) (hq : D.inclusion q ∈ c.chart.coordinates.source) :
    c.chart.coordinates (D.inclusion q) = ((chartAt ℂ i) q, 0) := by
  have hx := c.chart.r_normal (D.inclusion q) hq
  rw [r₁.retract] at hx
  have hy := c.chart.s_normal (D.inclusion q) hq
  rw [r₂.retract, ← hx] at hy
  have hyp : (c.chart.coordinates (D.inclusion q)).2 ^ n = 0 := by
    linear_combination -hy
  exact Prod.ext hx.symm (pow_eq_zero hyp)

/-- Reuse a fixed normal chart at another actual curve point in its source. -/
def recenter (q : D.curve) (hq : D.inclusion q ∈ c.chart.coordinates.source) :
    CenteredChart D U r₁ r₂ n i q where
  chart := c.chart
  source_mem := hq
  centre := c.centre_at q hq
  source_subset := c.source_subset
  holomorphic := c.holomorphic
  inverse_holomorphic := c.inverse_holomorphic

/-- The ordinary two-variable function in one fixed normal chart. -/
def family (r₃ : D.Retraction U) (w : ℂ × ℂ) : ℂ :=
  (chartAt ℂ i) (r₃.toFun (c.chart.coordinates.symm w)) - w.1

 theorem family_analytic (r₃ : D.Retraction U)
    (regularity : CoordinateCalculus.SurfaceAnalyticRegularity)
    (hi : p ∈ D.curve.chartDomain i) :
    AnalyticAt ℂ (c.family r₃) ((chartAt ℂ i) p, 0) := by
  apply regularity
  have ht : ((chartAt ℂ i) p, (0 : ℂ)) ∈ c.chart.coordinates.target := by
    rw [← c.centre]
    exact c.chart.coordinates.map_source c.source_mem
  have hto : Tendsto c.chart.coordinates.symm (𝓝 ((chartAt ℂ i) p, (0 : ℂ)))
      (𝓝 (D.inclusion p)) := by
    simpa only [show c.chart.coordinates.symm ((chartAt ℂ i) p, 0) = D.inclusion p
      from c.slice_zero] using (c.chart.coordinates.continuousAt_symm ht).tendsto
  have hr : Tendsto (fun w => r₃.toFun (c.chart.coordinates.symm w))
      (𝓝 ((chartAt ℂ i) p, (0 : ℂ))) (𝓝 p) := by
    have hc := (r₃.holomorphic.mdifferentiableAt
      (U.open_domain.mem_nhds (U.contains p))).continuousAt.tendsto
    simpa only [r₃.retract] using hc.comp hto
  filter_upwards [c.chart.coordinates.open_target.mem_nhds ht,
    hr ((chartAt ℂ i).open_source.mem_nhds hi)] with w hw hb
  have hinv := c.inverse_holomorphic.mdifferentiableAt
    (c.chart.coordinates.open_target.mem_nhds hw)
  have hr₃ := r₃.holomorphic.mdifferentiableAt (U.open_domain.mem_nhds
    (c.source_subset (c.chart.coordinates.map_target hw)))
  exact (mdifferentiableAt_iff_differentiableAt.mp
    (((mdifferentiable_chart i).mdifferentiableAt hb).comp w (hr₃.comp w hinv))).sub
      differentiableAt_fst

end CenteredChart

end Paper27.Geometry.RetractionCoefficientHolomorphic

namespace Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
open Paper27.Geometry.RetractionCoefficientHolomorphic
variable {X : CompactComplexSurface} {D : EmbeddedCurve X} {U : D.Neighbourhood}
  {r₁ r₂ r₃ : D.Retraction U} {n : ℕ}
variable (A : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)

/-- Turn a member of the actual normal atlas into a centred chart. -/
def centered (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    CenteredChart D U r₁ r₂ n i p where
  chart := A.chart i p
  source_mem := A.source_mem i p hi
  centre := A.centre i p hi
  source_subset := A.source_subset i p
  holomorphic := A.holomorphic i p
  inverse_holomorphic := A.inverse_holomorphic i p

/-- The actual Taylor coefficient computed with the chart selected at `(i,p)`. -/
def coefficient (J : TaylorGerms.TaylorCalculus) (r₃ : D.Retraction U)
    (k : ℕ) (i p : D.curve) : ℂ := (J.jet (2 * n) (A.third r₃ i p)).coeff k

 theorem coefficient_leading (J : TaylorGerms.TaylorCalculus) (r₃ : D.Retraction U)
    (ho : A.HasThirdOrder r₃) (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.coefficient J r₃ n i p = A.leading r₃ ho i p := by
  exact (J.order_factor (2 * n) n _ _ (by omega) (A.third_analytic r₃ i p hi)
    (A.thirdFactor_spec r₃ ho i p hi).1 (A.thirdFactor_spec r₃ ho i p hi).2.2).2

/-- Near a given point, the arbitrarily chosen coefficient agrees with the
ordinary parameter coefficient of one fixed actual normal chart. -/
 theorem coefficient_locally_fixed (J : TaylorGerms.TaylorCalculus) (r₃ : D.Retraction U)
    (hn : 0 < n) (k : ℕ) (hk : k ≤ 2 * n) (hkd : n ∣ k)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.coefficient J r₃ k i =ᶠ[𝓝 p]
      fun q => (J.jet (2 * n) (fun z =>
        (A.centered i p hi).family r₃ ((chartAt ℂ i) q, z))).coeff k := by
  have hsource : ∀ᶠ q in 𝓝 p, D.inclusion q ∈ (A.chart i p).coordinates.source :=
    D.inclusion.holomorphic.continuous.continuousAt
      ((A.chart i p).coordinates.open_source.mem_nhds (A.source_mem i p hi))
  filter_upwards [(chartAt ℂ i).open_source.mem_nhds hi, hsource] with q hqi hqs
  have hc := ((A.centered i p hi).recenter q hqs).coefficient_independent
    (A.centered i q hqi) J r₃ hn hqi (2 * n) k (by omega) hk hkd
  exact hc

/-- Both the n and 2n coefficients are holomorphic on the actual base chart,
although the chosen normal chart may vary arbitrarily with the centre. -/
 theorem coefficient_holomorphic (J : TaylorGerms.TaylorCalculus)
    (P : ParametricTaylorCalculus J) (r₃ : D.Retraction U)
    (hn : 0 < n) (k : ℕ) (hk : k ≤ 2 * n) (hkd : n ∣ k) (i : D.curve) :
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (A.coefficient J r₃ k i) (D.curve.chartDomain i) := by
  intro p hi
  have hF := (A.centered i p hi).family_analytic r₃ P.regularity hi
  have hparam := P.parameter_at (2 * n) k ((A.centered i p hi).family r₃)
    ((chartAt ℂ i) p) hF
  have hparam' := mdifferentiableAt_iff_differentiableAt.mpr hparam.differentiableAt
  have hcomp := hparam'.comp p ((mdifferentiable_chart i).mdifferentiableAt hi)
  exact (hcomp.congr_of_eventuallyEq
    (A.coefficient_locally_fixed J r₃ hn k hk hkd i p hi)).mdifferentiableWithinAt

/-- Changing every chosen normal chart leaves both relevant coefficients
unchanged, with no continuity assumed for the chart selection. -/
 theorem coefficient_independent_atlas (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)
    (J : TaylorGerms.TaylorCalculus) (r₃ : D.Retraction U) (hn : 0 < n)
    (k : ℕ) (hk : k ≤ 2 * n) (hkd : n ∣ k)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    B.coefficient J r₃ k i p = A.coefficient J r₃ k i p := by
  exact (A.centered i p hi).coefficient_independent (B.centered i p hi)
    J r₃ hn hi (2 * n) k (by omega) hk hkd

 theorem leading_holomorphic (J : TaylorGerms.TaylorCalculus)
    (P : ParametricTaylorCalculus J) (r₃ : D.Retraction U)
    (ho : A.HasThirdOrder r₃) (hn : 0 < n) (i : D.curve) :
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (A.leading r₃ ho i) (D.curve.chartDomain i) := by
  apply (A.coefficient_holomorphic J P r₃ hn n (by omega) (dvd_refl n) i).congr
  intro p hi
  exact (A.coefficient_leading J r₃ ho i p hi).symm

 theorem leading_independent_atlas (B : RetractionCoordinateGerms.NormalAtlas D U r₁ r₂ n)
    (J : TaylorGerms.TaylorCalculus) (r₃ : D.Retraction U)
    (hoA : A.HasThirdOrder r₃) (hoB : B.HasThirdOrder r₃) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    B.leading r₃ hoB i p = A.leading r₃ hoA i p := by
  rw [← B.coefficient_leading J r₃ hoB i p hi, ← A.coefficient_leading J r₃ hoA i p hi]
  exact A.coefficient_independent_atlas B J r₃ hn n (by omega) (dvd_refl n) i p hi

/-- The actual globally defined leading coefficient, evaluated using the
canonical chart at the point. Overlap compatibility makes the choice immaterial. -/
def globalLeading (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (p : D.curve) : ℂ :=
  A.leading r₃ ho p p

 theorem globalLeading_eq (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (hn : 0 < n)
    (i p : D.curve) (hi : p ∈ D.curve.chartDomain i) :
    A.globalLeading r₃ ho p = A.leading r₃ ho i p :=
  A.leading_overlap r₃ ho hn i p p hi (mem_chart_source ℂ p)

 theorem globalLeading_holomorphic (J : TaylorGerms.TaylorCalculus)
    (P : ParametricTaylorCalculus J) (r₃ : D.Retraction U)
    (ho : A.HasThirdOrder r₃) (hn : 0 < n) :
    MDifferentiable 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (A.globalLeading r₃ ho) := by
  intro p
  have hh := (A.leading_holomorphic J P r₃ ho hn p).mdifferentiableAt
    ((chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p))
  apply hh.congr_of_eventuallyEq
  filter_upwards [(chartAt ℂ p).open_source.mem_nhds (mem_chart_source ℂ p)] with q hq
  exact A.globalLeading_eq r₃ ho hn p q hq

/-- The remaining scalar multiplicity condition is on the actual difference
of the third and second retraction coordinates, never on a supplied a-function. -/
def HasDifferenceOrder (r₃ : D.Retraction U) : Prop :=
  ∀ i p, p ∈ D.curve.chartDomain i →
    analyticOrderAt (fun z => A.third r₃ i p z - z ^ n) 0 = n

/-- The difference appearing in the multiplicity condition is the difference
of the two actual written-coordinate retractions, on an actual normal slice. -/
 theorem coordinate_difference_germ (r₃ : D.Retraction U) (i p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) :
    (fun z => A.coordinate r₃ i p ((chartAt ℂ i) p, z) -
      A.coordinate r₂ i p ((chartAt ℂ i) p, z)) =ᶠ[𝓝 0]
      fun z => A.third r₃ i p z - z ^ n := by
  filter_upwards [A.slice_eventually i i p hi hi] with z hz
  have hs := (A.chart i p).s_normal (A.slice i p z) hz.2.1
  have hc : (A.chart i p).coordinates (A.slice i p z) = ((chartAt ℂ i) p, z) :=
    (A.chart i p).coordinates.right_inv hz.1
  rw [hc] at hs
  change (chartAt ℂ i) (r₃.toFun (A.slice i p z)) -
      (chartAt ℂ i) (r₂.toFun (A.slice i p z)) =
    ((chartAt ℂ i) (r₃.toFun (A.slice i p z)) - (chartAt ℂ i) p) - z ^ n
  rw [hs]
  ring

 theorem hasDifferenceOrder_of_coordinate_difference_order (r₃ : D.Retraction U)
    (hd : ∀ i p, p ∈ D.curve.chartDomain i →
      analyticOrderAt (fun z => A.coordinate r₃ i p ((chartAt ℂ i) p, z) -
        A.coordinate r₂ i p ((chartAt ℂ i) p, z)) 0 = n) : A.HasDifferenceOrder r₃ := by
  intro i p hi
  exact (analyticOrderAt_congr (A.coordinate_difference_germ r₃ i p hi)).symm.trans (hd i p hi)

 theorem hasDifferenceOrder_of_derivative_order (r₃ : D.Retraction U) (hn : 0 < n)
    (hd : ∀ i p, p ∈ D.curve.chartDomain i →
      analyticOrderAt (deriv (fun z => A.third r₃ i p z - z ^ n)) 0 = (n - 1 : ℕ)) :
    A.HasDifferenceOrder r₃ := by
  intro i p hi
  apply order_eq_of_derivative_order hn
    ((A.third_analytic r₃ i p hi).sub (analyticAt_id.pow n))
  · change A.third r₃ i p 0 - (0 : ℂ) ^ n = 0
    rw [A.third_zero r₃ i p hi, zero_pow (Nat.ne_of_gt hn), sub_self]
  · exact hd i p hi

/-- The actual leading coefficients glue on the compact curve and are one
constant different from zero and one. -/
 theorem leading_constant (J : TaylorGerms.TaylorCalculus) (P : ParametricTaylorCalculus J)
    (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (hdiff : A.HasDifferenceOrder r₃)
    (hn : 0 < n) :
    ∃ a : ℂ, a ≠ 0 ∧ a ≠ 1 ∧ ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a := by
  refine CoefficientGluing.leading_coefficient_constant D.curve D.curve.chartDomain
    (fun i => (chartAt ℂ i).open_source) (fun p => ⟨p, mem_chart_source ℂ p⟩)
    (A.leading r₃ ho) (A.leading_holomorphic J P r₃ ho hn)
    D.curve.chartJacobian ?_ ?_ n ?_ ?_
  · intro i j p hi hj
    rw [← A.normal_power_leading hn i j p hi hj]
    exact pow_ne_zero n (A.normal_derivative_ne_zero i j p hi hj)
  · exact A.leading_transition r₃ ho hn
  · exact A.leading_ne_zero r₃ ho
  · intro i p hi
    exact mul_ne_zero (by exact_mod_cast (Nat.ne_of_gt hn))
      (sub_ne_zero.mpr (A.leading_ne_one_of_difference_order r₃ ho i p hi (hdiff i p hi)))

/-- The 2n coefficient is holomorphic and well defined independently of the
normal-chart selection. This is the b-function needed by Appendix A. -/
 theorem doubleCoefficient_holomorphic (J : TaylorGerms.TaylorCalculus)
    (P : ParametricTaylorCalculus J) (r₃ : D.Retraction U) (hn : 0 < n)
    (ho : A.HasThirdOrder r₃) (T : TangentLineCocycle D.curve) (a : ℂ)
    (ha : ∀ i p, p ∈ D.curve.chartDomain i → A.leading r₃ ho i p = a) (i : D.curve) :
    MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
      ((A.toRetractionGerms r₃ ho T a ha).doubleCoefficient J i) (D.curve.chartDomain i) := by
  exact A.coefficient_holomorphic J P r₃ hn (2 * n) le_rfl (dvd_mul_left n 2) i

/-- All holomorphic coefficient hypotheses of the previously proved connection
construction are discharged from actual charts and retractions. -/
 theorem exists_tangent_connection (J : TaylorGerms.TaylorCalculus)
    (P : ParametricTaylorCalculus J) (r₃ : D.Retraction U)
    (ho : A.HasThirdOrder r₃) (hdiff : A.HasDifferenceOrder r₃)
    (hn : 2 ≤ n) (T : TangentLineCocycle D.curve) : Nonempty T.bundle.Connection := by
  obtain ⟨a, ha0, ha1, ha⟩ := A.leading_constant J P r₃ ho hdiff (by omega)
  exact ⟨(A.toRetractionGerms r₃ ho T a ha).connection J hn ha0 ha1
    (A.doubleCoefficient_holomorphic J P r₃ (by omega) ho T a ha)⟩

/-- The resulting connection contradicts the negative tangent degree of the
actual hyperbolic curve, using only the universal line-bundle degree laws. -/
 theorem common_tangency_impossible (J : TaylorGerms.TaylorCalculus)
    (P : ParametricTaylorCalculus J) (theory : LineBundleDegreeTheory)
    (r₃ : D.Retraction U) (ho : A.HasThirdOrder r₃) (hdiff : A.HasDifferenceOrder r₃)
    (hn : 2 ≤ n) (T : TangentLineCocycle D.curve) (hg : D.curve.Hyperbolic) : False := by
  have hz := theory.connection_degree_zero D.curve T.bundle
    (A.exists_tangent_connection J P r₃ ho hdiff hn T)
  have ht := theory.tangent_degree D.curve T
  have hg' : (2 : ℤ) ≤ D.curve.genus := by exact_mod_cast hg
  omega

end Paper27.Geometry.RetractionCoordinateGerms.NormalAtlas
