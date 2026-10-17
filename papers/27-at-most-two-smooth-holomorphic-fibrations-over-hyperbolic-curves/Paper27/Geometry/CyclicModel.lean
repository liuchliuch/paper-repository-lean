import Paper27.LocalProjection
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.OpenPartialHomeomorph
import Mathlib.Topology.Separation.Basic

/-!
# Reading the differential consequences of a cyclic normal form

This file does not assert the existence of the cyclic normal form in
Proposition 2.4. It proves consequences of an actual local coordinate identity
`(F,G) = (x, y^n + φ(x))`. The coordinate is an actual open partial
homeomorphism, analytic in both directions with bijective actual derivative.
The exponent is positive, as for the index of a finite cyclic cover; neither
`n ≥ 2` nor a nonzero graph derivative is an input.

At a ramification point, `n ≥ 2` is proved. The actual local ramification set is
then precisely `y = 0`. If `G` is a submersion, the graph derivative on that
curve is nonzero. The actual restrictions of both projections to its
coordinate parametrization have nonzero derivatives.

Positivity is necessary: with `n = 0`, `F=x`, `G=x+1`, and `φ=x`, both maps are
submersions and their pair is ramified, but its fibres are infinite.
-/

noncomputable section

open scoped Topology

namespace Paper27.Geometry.CyclicModel

/-- The full derivative of the actual coordinate model. -/
def jointDifferential (n : ℕ) (w a : ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (ContinuousLinearMap.fst ℂ ℂ ℂ).prod (localSecondDifferential n w a)

@[simp] theorem jointDifferential_apply (n : ℕ) (w a : ℂ) (v : ℂ × ℂ) :
    jointDifferential n w a v = (v.1, (n : ℂ) * w ^ (n - 1) * v.2 + a * v.1) := by
  simp [jointDifferential, localSecondDifferential_apply]

theorem hasFDerivAt_model (n : ℕ) {φ : ℂ → ℂ} {q : ℂ × ℂ}
    (hφ : HasDerivAt φ (deriv φ q.1) q.1) :
    HasFDerivAt (localBranchMap n φ)
      (jointDifferential n q.2 (deriv φ q.1)) q := by
  have hs := hasFDerivAt_localSecondProjection n (t := q.1) (w := q.2) hφ
  simpa only [localBranchMap, localSecondProjection, jointDifferential, Prod.eta] using
    (hasFDerivAt_fst (𝕜 := ℂ) (p := q)).prodMk hs

theorem jointDifferential_surjective_iff (n : ℕ) (w a : ℂ) :
    Function.Surjective (jointDifferential n w a) ↔ (n : ℂ) * w ^ (n - 1) ≠ 0 := by
  constructor
  · intro hs hzero
    obtain ⟨v, hv⟩ := hs (0, 1)
    have hv₁ : v.1 = 0 := congrArg Prod.fst hv
    have hv₂ := congrArg Prod.snd hv
    have hfalse : (0 : ℂ) = 1 := by
      simpa only [jointDifferential_apply, hzero, hv₁, mul_zero, zero_mul, zero_add] using hv₂
    exact zero_ne_one hfalse
  · intro hcoef y
    refine ⟨(y.1, (y.2 - a * y.1) / ((n : ℂ) * w ^ (n - 1))), ?_⟩
    apply Prod.ext
    · rfl
    · simp [jointDifferential_apply, mul_div_cancel₀, hcoef]

theorem coefficient_ne_zero_iff (n : ℕ) (hn : 2 ≤ n) (w : ℂ) :
    (n : ℂ) * w ^ (n - 1) ≠ 0 ↔ w ≠ 0 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpred : n - 1 ≠ 0 := by omega
  constructor
  · intro h hw
    apply h
    simp [hw, zero_pow hpred]
  · intro hw
    exact mul_ne_zero hn0 (pow_ne_zero _ hw)

/-- A genuine complex coordinate change, retaining both analytic directions
and the actual nonsingular derivative, as supplied by a holomorphic chart. -/
structure AnalyticCoordinateChart (p : ℂ × ℂ) where
  chart : OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ)
  source_mem : p ∈ chart.source
  analytic : ∀ q ∈ chart.source, AnalyticAt ℂ chart q
  inverse_analytic : ∀ z ∈ chart.target, AnalyticAt ℂ chart.symm z
  differential_bijective : ∀ q ∈ chart.source, Function.Bijective (fderiv ℂ chart q)

/-- The actual normal-form identity furnished by a finite cyclic-germ
classification. Only the positive index is assumed, not the conclusions below. -/
structure CyclicNormalForm (F G : ℂ × ℂ → ℂ) (p : ℂ × ℂ) where
  coordinate : AnalyticCoordinateChart p
  centre_x : ℂ
  centre_coordinates : coordinate.chart p = (centre_x, 0)
  exponent : ℕ
  exponent_positive : 0 < exponent
  graph : ℂ → ℂ
  graph_analytic : ∀ q ∈ coordinate.chart.source,
    AnalyticAt ℂ graph (coordinate.chart q).1
  identity : ∀ q ∈ coordinate.chart.source,
    (F q, G q) = localBranchMap exponent graph (coordinate.chart q)

namespace CyclicNormalForm

variable {F G : ℂ × ℂ → ℂ} {p : ℂ × ℂ}

theorem hasFDerivAt_pair (B : CyclicNormalForm F G p) {q : ℂ × ℂ}
    (hq : q ∈ B.coordinate.chart.source) :
    HasFDerivAt (fun z => (F z, G z))
      ((jointDifferential B.exponent (B.coordinate.chart q).2
        (deriv B.graph (B.coordinate.chart q).1)).comp
          (fderiv ℂ B.coordinate.chart q)) q := by
  have hmodel := hasFDerivAt_model B.exponent
    (B.graph_analytic q hq).differentiableAt.hasDerivAt
  have hcomp := hmodel.comp q (B.coordinate.analytic q hq).differentiableAt.hasFDerivAt
  apply hcomp.congr_of_eventuallyEq
  exact Filter.eventually_of_mem (B.coordinate.chart.open_source.mem_nhds hq)
    fun z hz => B.identity z hz

theorem hasFDerivAt_first (B : CyclicNormalForm F G p) {q : ℂ × ℂ}
    (hq : q ∈ B.coordinate.chart.source) :
    HasFDerivAt F ((ContinuousLinearMap.fst ℂ ℂ ℂ).comp
      (fderiv ℂ B.coordinate.chart q)) q := by
  have hcomp := (hasFDerivAt_fst (𝕜 := ℂ) (p := B.coordinate.chart q)).comp q
    (B.coordinate.analytic q hq).differentiableAt.hasFDerivAt
  apply hcomp.congr_of_eventuallyEq
  exact Filter.eventually_of_mem (B.coordinate.chart.open_source.mem_nhds hq)
    fun z hz => congrArg Prod.fst (B.identity z hz)

theorem hasFDerivAt_second (B : CyclicNormalForm F G p) {q : ℂ × ℂ}
    (hq : q ∈ B.coordinate.chart.source) :
    HasFDerivAt G ((localSecondDifferential B.exponent (B.coordinate.chart q).2
      (deriv B.graph (B.coordinate.chart q).1)).comp
        (fderiv ℂ B.coordinate.chart q)) q := by
  have hs := hasFDerivAt_localSecondProjection B.exponent
    (t := (B.coordinate.chart q).1) (w := (B.coordinate.chart q).2)
    (B.graph_analytic q hq).differentiableAt.hasDerivAt
  have hcomp := hs.comp q (B.coordinate.analytic q hq).differentiableAt.hasFDerivAt
  apply hcomp.congr_of_eventuallyEq
  exact Filter.eventually_of_mem (B.coordinate.chart.open_source.mem_nhds hq)
    fun z hz => congrArg Prod.snd (B.identity z hz)

theorem pair_surjective_iff_coefficient (B : CyclicNormalForm F G p) {q : ℂ × ℂ}
    (hq : q ∈ B.coordinate.chart.source) :
    Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) ↔
      (B.exponent : ℂ) * (B.coordinate.chart q).2 ^ (B.exponent - 1) ≠ 0 := by
  rw [(B.hasFDerivAt_pair hq).fderiv]
  change Function.Surjective (jointDifferential B.exponent (B.coordinate.chart q).2
      (deriv B.graph (B.coordinate.chart q).1) ∘ fderiv ℂ B.coordinate.chart q) ↔ _
  rw [Function.Surjective.of_comp_iff _ (B.coordinate.differential_bijective q hq).2]
  exact jointDifferential_surjective_iff _ _ _

/-- Positivity of the covering index and actual ramification exclude index one. -/
theorem exponent_ge_two (B : CyclicNormalForm F G p)
    (hp : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) p)) :
    2 ≤ B.exponent := by
  have hn1 : B.exponent ≠ 1 := by
    intro hn
    apply hp
    apply (B.pair_surjective_iff_coefficient B.coordinate.source_mem).mpr
    simp [hn]
  have hpositive := B.exponent_positive
  omega

/-- The actual local ramification condition is exactly the normal coordinate
`y=0`, not merely a subset of that locus. -/
theorem ramification_iff_normal_zero (B : CyclicNormalForm F G p)
    (hp : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) p))
    {q : ℂ × ℂ} (hq : q ∈ B.coordinate.chart.source) :
    ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q) ↔
      (B.coordinate.chart q).2 = 0 := by
  rw [B.pair_surjective_iff_coefficient hq,
    coefficient_ne_zero_iff B.exponent (B.exponent_ge_two hp)]
  simp only [not_not]

theorem ramification_set_eq (B : CyclicNormalForm F G p)
    (hp : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) p)) :
    {q : ℂ × ℂ | q ∈ B.coordinate.chart.source ∧
      ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) q)} =
      {q : ℂ × ℂ | q ∈ B.coordinate.chart.source ∧ (B.coordinate.chart q).2 = 0} := by
  ext q
  exact and_congr_right fun hq => B.ramification_iff_normal_zero hp hq

/-- The first projection is automatically a genuine submersion. -/
theorem first_surjective (B : CyclicNormalForm F G p) {q : ℂ × ℂ}
    (hq : q ∈ B.coordinate.chart.source) : Function.Surjective (fderiv ℂ F q) := by
  rw [(B.hasFDerivAt_first hq).fderiv]
  intro a
  obtain ⟨v, hv⟩ := (B.coordinate.differential_bijective q hq).2 (a, 0)
  exact ⟨v, congrArg Prod.fst hv⟩

/-- Smoothness of the actual second projection forces a nonzero graph
derivative along the normal curve. -/
theorem graph_derivative_ne_zero (B : CyclicNormalForm F G p)
    (hp : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) p))
    {q : ℂ × ℂ} (hq : q ∈ B.coordinate.chart.source)
    (hy : (B.coordinate.chart q).2 = 0) (hG : Function.Surjective (fderiv ℂ G q)) :
    deriv B.graph (B.coordinate.chart q).1 ≠ 0 := by
  rw [(B.hasFDerivAt_second hq).fderiv] at hG
  change Function.Surjective (localSecondDifferential B.exponent (B.coordinate.chart q).2
    (deriv B.graph (B.coordinate.chart q).1) ∘ fderiv ℂ B.coordinate.chart q) at hG
  have hm := Function.Surjective.of_comp hG
  have hc := (localSecondDifferential_surjective_iff B.exponent (B.exponent_ge_two hp)
    (B.coordinate.chart q).2 (deriv B.graph (B.coordinate.chart q).1)).mp hm
  exact hc.resolve_left (fun hn => hn hy)

/-- The actual coordinate parametrization of the reduced normal curve. -/
def normalCurve (B : CyclicNormalForm F G p) (x : ℂ) : ℂ × ℂ :=
  B.coordinate.chart.symm (x, 0)

theorem centre_x_mem_target (B : CyclicNormalForm F G p) :
    (B.centre_x, (0 : ℂ)) ∈ B.coordinate.chart.target := by
  rw [← B.centre_coordinates]
  exact B.coordinate.chart.map_source B.coordinate.source_mem

theorem normalCurve_centre (B : CyclicNormalForm F G p) : B.normalCurve B.centre_x = p := by
  change B.coordinate.chart.symm (B.centre_x, 0) = p
  rw [← B.centre_coordinates]
  exact B.coordinate.chart.left_inv B.coordinate.source_mem

theorem analyticAt_normalCurve (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) : AnalyticAt ℂ B.normalCurve x :=
  (B.coordinate.inverse_analytic (x, 0) hx).comp
    (f := fun t : ℂ => (t, (0 : ℂ))) (x := x) (analyticAt_id.prod analyticAt_const)

theorem normalCurve_mem_source (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) :
    B.normalCurve x ∈ B.coordinate.chart.source := B.coordinate.chart.map_target hx

theorem coordinates_normalCurve (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) :
    B.coordinate.chart (B.normalCurve x) = (x, 0) := B.coordinate.chart.right_inv hx

theorem normalCurve_first (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) : F (B.normalCurve x) = x := by
  have hid := B.identity _ (B.normalCurve_mem_source hx)
  rw [B.coordinates_normalCurve hx] at hid
  exact congrArg Prod.fst hid

theorem normalCurve_second (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) : G (B.normalCurve x) = B.graph x := by
  have hid := B.identity _ (B.normalCurve_mem_source hx)
  rw [B.coordinates_normalCurve hx] at hid
  simpa only [localBranchMap, zero_pow (Nat.ne_of_gt B.exponent_positive), zero_add] using
    congrArg Prod.snd hid

theorem hasDerivAt_first_normalCurve (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) :
    HasDerivAt (F ∘ B.normalCurve) 1 x := by
  apply (hasDerivAt_id x).congr_of_eventuallyEq
  have hU : ((fun t : ℂ => (t, (0 : ℂ))) ⁻¹' B.coordinate.chart.target) ∈ 𝓝 x :=
    (B.coordinate.chart.open_target.preimage (continuous_id.prodMk continuous_const)).mem_nhds hx
  exact Filter.eventually_of_mem hU fun t ht => B.normalCurve_first ht

theorem hasDerivAt_second_normalCurve (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) :
    HasDerivAt (G ∘ B.normalCurve) (deriv B.graph x) x := by
  have hφ : HasDerivAt B.graph (deriv B.graph x) x := by
    simpa only [B.coordinates_normalCurve hx] using
      (B.graph_analytic _ (B.normalCurve_mem_source hx)).differentiableAt.hasDerivAt
  apply hφ.congr_of_eventuallyEq
  have hU : ((fun t : ℂ => (t, (0 : ℂ))) ⁻¹' B.coordinate.chart.target) ∈ 𝓝 x :=
    (B.coordinate.chart.open_target.preimage (continuous_id.prodMk continuous_const)).mem_nhds hx
  exact Filter.eventually_of_mem hU fun t ht => B.normalCurve_second ht

/-- The normal-curve parametrization is an actual holomorphic immersion. -/
theorem normalCurve_derivative_ne_zero (B : CyclicNormalForm F G p) {x : ℂ}
    (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target) : deriv B.normalCurve x ≠ 0 := by
  have hchain := (B.hasFDerivAt_first (B.normalCurve_mem_source hx)).comp_hasDerivAt x
    (B.analyticAt_normalCurve hx).differentiableAt.hasDerivAt
  have heq := hchain.unique (B.hasDerivAt_first_normalCurve hx)
  intro hz
  rw [hz, map_zero] at heq
  exact zero_ne_one heq

/-- Both actual restrictions to the normal curve are unramified. The first
derivative is one, and the second is nonzero because the original `G` is a
submersion there. Neither nonvanishing assertion is an input. -/
theorem normalCurve_projections_unramified (B : CyclicNormalForm F G p)
    (hp : ¬ Function.Surjective (fderiv ℂ (fun z => (F z, G z)) p))
    {x : ℂ} (hx : (x, (0 : ℂ)) ∈ B.coordinate.chart.target)
    (hG : Function.Surjective (fderiv ℂ G (B.normalCurve x))) :
    deriv (F ∘ B.normalCurve) x ≠ 0 ∧ deriv (G ∘ B.normalCurve) x ≠ 0 := by
  have hφ : deriv B.graph x ≠ 0 := by
    have h := B.graph_derivative_ne_zero hp (B.normalCurve_mem_source hx)
      (by rw [B.coordinates_normalCurve hx]) hG
    simpa only [B.coordinates_normalCurve hx] using h
  constructor
  · rw [(B.hasDerivAt_first_normalCurve hx).deriv]
    exact one_ne_zero
  · rw [(B.hasDerivAt_second_normalCurve hx).deriv]
    exact hφ

end CyclicNormalForm

end Paper27.Geometry.CyclicModel
