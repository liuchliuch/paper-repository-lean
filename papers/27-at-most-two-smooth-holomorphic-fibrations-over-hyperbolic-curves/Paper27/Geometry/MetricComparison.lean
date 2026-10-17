import Paper27.Geometry.Objects
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Finsupp.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The metric-comparison part of Lemma 2.3

The maps, their coordinate derivatives, and their ramification orders below are
actual functions on the complex manifolds in `Objects`. No divisor is supplied
as an unrelated label. A conformal metric is represented by the nonnegative
coefficient of its quadratic form in the preferred tangent coordinate at each
point. `densityInChart` changes that coefficient by the actual differential of
the inverse chart. Thus the cone and curvature predicates are statements about
specified real functions, not an unspecified `HasMetric` proposition.

Three classical inputs are kept separate and universally quantified:

* `ClassicalCurveMapFacts`: finite zeros/fibres, finite analytic order, and
  Riemann--Hurwitz for nonconstant holomorphic maps of compact curves.
  Forster, *Lectures on Riemann Surfaces*, Theorems 2.1 and 4.24 supply
  the local normal form and finite fibre degree. Troyanov, loc. cit.,
  Corollary 2, p. 801, states Riemann--Hurwitz for the pulled-back divisor;
* `ClassicalPullbackFacts`: the local expression of a pulled-back smooth
  conformal metric and preservation of Gaussian curvature off ramification.
  Troyanov, loc. cit., §1.3, p. 799, defines the pulled-back divisor by
  `m + (m+1)β` at an ordinary branch point of order `m`; the proof of
  Corollary 2, p. 801, explicitly states that the pulled-back metric represents
  that divisor;
* `TroyanovUniqueness`: only the uniqueness part of Troyanov, *Prescribing
  curvature on compact surfaces with conical singularities*, Trans. AMS 324
  (1991), Theorem A, p. 793. Original author PDF:
  https://sma.epfl.ch/~troyanov/Papers/Prescribing.pdf .

The cone-angle arithmetic, the negative Euler-number check, and comparison of
two pullbacks with the same ramification orders are proved here. These inputs
do not include the graph-of-local-isometry assertion of Lemma 2.3. The final
identity-principle lemma proves the continuation step for actual coordinate
functions once a local isometry and a regular germ have been constructed.

The usual identification of `2 - 2 * genus` with the surface Euler
characteristic, and the compatibility of the displayed coordinate metric
representation with intrinsic conformal tensors, are part of the classical
interfaces' mathematical interpretation; they are not independently proved in
this file. Existence of the smooth hyperbolic metrics is also not asserted.
-/

noncomputable section

open scoped Manifold Topology BigOperators
open Filter

namespace Paper27.Geometry.MetricComparison

/-- The actual coordinate expression near `p`; only its germ at the centre of
the chart is used. -/
def writtenCoordinateMap {D B : Curve} (u : HolomorphicMap D B) (p : D) : ℂ → ℂ :=
  chartAt ℂ (u p) ∘ u ∘ (chartAt ℂ p).symm

/-- The actual zero order of the derivative, not a freely assigned divisor.
For a nonconstant curve map the finiteness/analyticity inputs below rule out
the junk cases in the definition of `analyticOrderNatAt`. -/
def ramificationOrder {D B : Curve} (u : HolomorphicMap D B) (p : D) : ℕ :=
  analyticOrderNatAt (deriv (writtenCoordinateMap u p)) (chartAt ℂ p p)

def Nonconstant {D B : Curve} (u : HolomorphicMap D B) : Prop :=
  ∃ p q : D, u p ≠ u q

/-- The Euler characteristic written in terms of the actual topological genus
defined in `Objects`; surface classification identifies it with topological χ. -/
def eulerCharacteristic (D : Curve) : ℝ := 2 - 2 * (D.genus : ℝ)

abbrev RamificationSupportFinite {D B : Curve} (u : HolomorphicMap D B) :=
  (Function.support (ramificationOrder u)).Finite

def ramificationDivisor {D B : Curve} (u : HolomorphicMap D B)
    (h : RamificationSupportFinite u) : D →₀ ℕ :=
  Finsupp.ofSupportFinite (ramificationOrder u) h

@[simp] theorem ramificationDivisor_apply {D B : Curve} (u : HolomorphicMap D B)
    (h : RamificationSupportFinite u) (p : D) :
    ramificationDivisor u h p = ramificationOrder u p := rfl

/-- The real degree of an effective divisor. -/
def divisorDegree {D : Curve} (R : D →₀ ℕ) : ℝ :=
  ∑ p ∈ R.support, (R p : ℝ)

theorem divisorDegree_nonnegative {D : Curve} (R : D →₀ ℕ) :
    0 ≤ divisorDegree R := by
  exact Finset.sum_nonneg (fun p _ => Nat.cast_nonneg (R p))

/-- A concrete degree, counting local multiplicities over the chosen point of
the target. Independence of the chosen regular or branch value is classical. -/
def mapDegree {D B : Curve} (u : HolomorphicMap D B)
    (hf : {p : D | u p = B.basepoint}.Finite) : ℕ :=
  ∑ p ∈ hf.toFinset, (ramificationOrder u p + 1)

/-- Standard curve-map facts, all stated for the actual holomorphic map and
its actual coordinate derivative. Riemann--Hurwitz is the usual
`χ(D) + deg R(u) = deg(u) χ(B)`; it is not Lemma 2.3. -/
structure ClassicalCurveMapFacts : Prop where
  derivative_analytic : ∀ (D B : Curve) (u : HolomorphicMap D B), Nonconstant u →
    ∀ p : D, AnalyticAt ℂ (deriv (writtenCoordinateMap u p)) (chartAt ℂ p p)
  derivative_order_finite : ∀ (D B : Curve) (u : HolomorphicMap D B), Nonconstant u →
    ∀ p : D, analyticOrderAt (deriv (writtenCoordinateMap u p)) (chartAt ℂ p p) ≠ ⊤
  ramification_finite : ∀ (D B : Curve) (u : HolomorphicMap D B), Nonconstant u →
    RamificationSupportFinite u
  fibres_finite : ∀ (D B : Curve) (u : HolomorphicMap D B), Nonconstant u →
    ∀ b : B, {p : D | u p = b}.Finite
  surjective : ∀ (D B : Curve) (u : HolomorphicMap D B), Nonconstant u →
    Function.Surjective u
  riemann_hurwitz : ∀ (D B : Curve) (u : HolomorphicMap D B) (_hu : Nonconstant u)
    (hr : RamificationSupportFinite u) (hf : {p : D | u p = B.basepoint}.Finite),
    eulerCharacteristic D + divisorDegree (ramificationDivisor u hr) =
      (mapDegree u hf : ℝ) * eulerCharacteristic B

/-- Mathlib's analytic factorization theorem gives the actual local
derivative factor. Only analyticity and finiteness of the map's derivative
order are taken from the general curve-map interface. -/
theorem derivative_factorization (maps : ClassicalCurveMapFacts)
    {D B : Curve} (u : HolomorphicMap D B) (hu : Nonconstant u) (p : D) :
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a (chartAt ℂ p p) ∧ a (chartAt ℂ p p) ≠ 0 ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p),
        deriv (writtenCoordinateMap u p) z =
          (z - chartAt ℂ p p) ^ ramificationOrder u p * a z := by
  have ha := maps.derivative_analytic D B u hu p
  have hf := maps.derivative_order_finite D B u hu p
  simpa only [ramificationOrder, smul_eq_mul] using
    (ha.analyticOrderNatAt_eq_iff hf).mp rfl

/-- With the classical analytic/finiteness facts, order zero is equivalent
to a nonzero actual coordinate differential. -/
theorem ramificationOrder_eq_zero_iff (maps : ClassicalCurveMapFacts)
    {D B : Curve} (u : HolomorphicMap D B) (hu : Nonconstant u) (p : D) :
    ramificationOrder u p = 0 ↔
      deriv (writtenCoordinateMap u p) (chartAt ℂ p p) ≠ 0 := by
  have ha := maps.derivative_analytic D B u hu p
  have hf := maps.derivative_order_finite D B u hu p
  constructor
  · intro hzero
    have hcast := Nat.cast_analyticOrderNatAt hf
    change (ramificationOrder u p : ℕ∞) = _ at hcast
    rw [hzero] at hcast
    exact ha.analyticOrderAt_eq_zero.mp hcast.symm
  · intro hderiv
    have hzero := ha.analyticOrderAt_eq_zero.mpr hderiv
    simp only [ramificationOrder, analyticOrderNatAt, hzero, ENat.toNat_zero]

/-- The coefficient of a conformal quadratic form in each preferred tangent
frame. Its value on a tangent vector `v` is `weight p * ‖v‖²`. Nonnegative
coefficients allow the zeroes of pulled-back metrics at branch points. -/
@[ext] structure ConformalMetric (D : Curve) where
  weight : D → ℝ
  nonnegative : ∀ p, 0 ≤ weight p

/-- Mathlib deliberately gives no canonical norm to a manifold tangent
space. This is its complex coordinate in the preferred tangent frame,
rather than an intrinsic norm on that tangent space. -/
def tangentCoordinate {D : Curve} (p : D)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) : ℂ := v

def squaredNorm {D : Curve} (g : ConformalMetric D) (p : D)
    (v : TangentSpace 𝓘(ℂ, ℂ) p) : ℝ := g.weight p * ‖tangentCoordinate p v‖ ^ 2

/-- The density in the chart at `p`, using the actual tangent map of the
inverse chart. It is considered only on that chart's target. -/
def densityInChart {D : Curve} (g : ConformalMetric D) (p : D) (z : ℂ) : ℝ :=
  g.weight ((chartAt ℂ p).symm z) *
    ‖tangentCoordinate ((chartAt ℂ p).symm z)
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (chartAt ℂ p).symm z (1 : ℂ))‖ ^ 2

/-- The pullback is a defined quadratic-form coefficient, not an additional
metric whose relation to the map is left unspecified. -/
def pullback {D B : Curve} (u : HolomorphicMap D B) (g : ConformalMetric B) :
    ConformalMetric D where
  weight p := g.weight (u p) *
    ‖tangentCoordinate (u p) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p (1 : ℂ))‖ ^ 2
  nonnegative _p := mul_nonneg (g.nonnegative _) (sq_nonneg _)

/-- Equality of these concrete metrics is exactly equality of their
quadratic forms on the actual tangent spaces. -/
theorem metric_eq_iff_squaredNorm {D : Curve} (g h : ConformalMetric D) :
    g = h ↔ ∀ p (v : TangentSpace 𝓘(ℂ, ℂ) p),
      squaredNorm g p v = squaredNorm h p v := by
  constructor
  · intro heq
    subst h
    intro p v
    rfl
  · intro heq
    ext p
    simpa only [squaredNorm, tangentCoordinate, norm_one, one_pow, mul_one] using
      heq p (1 : ℂ)

/-- The defined coefficient really is the pullback quadratic form under the
actual manifold differential. This uses only its complex linearity. -/
theorem pullback_squaredNorm {D B : Curve} (u : HolomorphicMap D B)
    (g : ConformalMetric B) (p : D) (v : TangentSpace 𝓘(ℂ, ℂ) p) :
    squaredNorm (pullback u g) p v =
      squaredNorm g (u p) (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p v) := by
  let A : ℂ →L[ℂ] ℂ := mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) u p
  let w : ℂ := v
  have hA : A w = w * A 1 := by
    simpa only [smul_eq_mul, mul_one] using A.map_smul w (1 : ℂ)
  change (g.weight (u p) * ‖A 1‖ ^ 2) * ‖w‖ ^ 2 = g.weight (u p) * ‖A w‖ ^ 2
  rw [hA, norm_mul, mul_pow]
  ring

/-- Integer cone data sufficient for pullbacks by holomorphic curve maps.
The exponent `m` gives cone angle `2π(m+1)`. The smooth positive factor is
specified near every point, including the points with exponent zero. -/
def HasConeData {D : Curve} (g : ConformalMetric D) (R : D →₀ ℕ) : Prop :=
  ∀ p : D, ∃ h : ℂ → ℝ,
    ContDiffAt ℝ ⊤ h (chartAt ℂ p p) ∧ 0 < h (chartAt ℂ p p) ∧
      ∀ᶠ z in 𝓝 (chartAt ℂ p p), densityInChart g p z =
        ‖z - chartAt ℂ p p‖ ^ (2 * R p) * h z

/-- The ordinary Euclidean Laplacian in the chart `ℂ = ℝ²`. -/
def laplacian (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  fderiv ℝ (fun w => fderiv ℝ f w (1 : ℂ)) z (1 : ℂ) +
    fderiv ℝ (fun w => fderiv ℝ f w Complex.I) z Complex.I

/-- For `g = ρ |dz|²`, `Δ log ρ = -2 K ρ` away from its cone points.
The predicate is checked at every regular point in its actual chart. -/
def HasConstantCurvature {D : Curve} (g : ConformalMetric D) (R : D →₀ ℕ)
    (K : ℝ) : Prop :=
  ∀ p : D, R p = 0 →
    laplacian (fun z => Real.log (densityInChart g p z)) (chartAt ℂ p p) =
      -2 * K * densityInChart g p (chartAt ℂ p p)

def coneAngle {D : Curve} (R : D →₀ ℕ) (p : D) : ℝ :=
  2 * Real.pi * ((R p : ℝ) + 1)

theorem coneAngle_positive {D : Curve} (R : D →₀ ℕ) (p : D) :
    0 < coneAngle R p := by
  unfold coneAngle
  positivity

theorem coneAngle_defect {D : Curve} (R : D →₀ ℕ) (p : D) :
    coneAngle R p - 2 * Real.pi = 2 * Real.pi * (R p : ℝ) := by
  unfold coneAngle
  ring

/-- The finite angle correction in Troyanov's hypothesis. -/
theorem totalConeDefect {D : Curve} (R : D →₀ ℕ) :
    (∑ p ∈ R.support, (coneAngle R p - 2 * Real.pi)) =
      2 * Real.pi * divisorDegree R := by
  simp_rw [coneAngle_defect]
  rw [divisorDegree, Finset.mul_sum]

theorem troyanov_angle_condition {D : Curve} (R : D →₀ ℕ)
    (h : eulerCharacteristic D + divisorDegree R < 0) :
    2 * Real.pi * eulerCharacteristic D +
      (∑ p ∈ R.support, (coneAngle R p - 2 * Real.pi)) < 0 := by
  rw [totalConeDefect, ← mul_add]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) Real.pi_pos) h

/-- The exact uniqueness assertion used from Troyanov Theorem A, restricted
to the positive integer cone angles arising here and constant curvature -1.
It quantifies over all compact connected complex curves, divisors, and the
concrete metrics above. Existence and the graph assertion are not included. -/
def TroyanovUniqueness : Prop :=
  ∀ (D : Curve) (R : D →₀ ℕ) (g h : ConformalMetric D),
    eulerCharacteristic D + divisorDegree R < 0 →
    HasConeData g R → HasConeData h R →
    HasConstantCurvature g R (-1) → HasConstantCurvature h R (-1) → g = h

/-- General local pullback facts, for every smooth curvature -1 metric on a
target curve. The cone statement is the standard local derivative-zero
calculation; the curvature statement is invariance under a local conformal
diffeomorphism. Neither compares two maps or asserts their graph property. -/
structure ClassicalPullbackFacts : Prop where
  cone_data : ∀ (D B : Curve) (u : HolomorphicMap D B), Nonconstant u →
    ∀ (hr : RamificationSupportFinite u) (g : ConformalMetric B),
    HasConeData g 0 → HasConeData (pullback u g) (ramificationDivisor u hr)
  curvature : ∀ (D B : Curve) (u : HolomorphicMap D B), Nonconstant u →
    ∀ (hr : RamificationSupportFinite u) (g : ConformalMetric B),
    HasConeData g 0 → HasConstantCurvature g 0 (-1) →
      HasConstantCurvature (pullback u g) (ramificationDivisor u hr) (-1)

theorem hyperbolic_euler_negative {B : Curve} (hB : B.Hyperbolic) :
    eulerCharacteristic B < 0 := by
  have h : (2 : ℝ) ≤ (B.genus : ℝ) := by exact_mod_cast hB
  unfold eulerCharacteristic
  linarith

/-- The concrete fibre-counting degree is positive because the nonconstant
map is surjective and every local multiplicity is at least one. -/
theorem mapDegree_positive {D B : Curve} (u : HolomorphicMap D B)
    (hf : {p : D | u p = B.basepoint}.Finite) (hs : Function.Surjective u) :
    0 < mapDegree u hf := by
  obtain ⟨p, hp⟩ := hs B.basepoint
  unfold mapDegree
  apply Finset.sum_pos'
  · intro q _
    exact Nat.zero_le _
  · exact ⟨p, hf.mem_toFinset.mpr hp, Nat.succ_pos _⟩

/-- Riemann--Hurwitz supplies the equality. The strict sign needed for
Troyanov follows here from the actual target genus and positive map degree. -/
theorem negative_cone_euler (maps : ClassicalCurveMapFacts)
    {D B : Curve} (u : HolomorphicMap D B) (hu : Nonconstant u)
    (hB : B.Hyperbolic) (hr : RamificationSupportFinite u) :
    eulerCharacteristic D + divisorDegree (ramificationDivisor u hr) < 0 := by
  let hf := maps.fibres_finite D B u hu B.basepoint
  rw [maps.riemann_hurwitz D B u hu hr hf]
  have hdeg : (0 : ℝ) < (mapDegree u hf : ℝ) := by
    exact_mod_cast mapDegree_positive u hf (maps.surjective D B u hu)
  exact mul_neg_of_pos_of_neg hdeg (hyperbolic_euler_negative hB)

/-- In particular, any compact curve mapping nonconstantly to a hyperbolic
curve is itself hyperbolic. This supplies the genus check for a normalized
ramification component in Proposition 2.4 without assuming it as a label. -/
theorem source_hyperbolic (maps : ClassicalCurveMapFacts)
    {D B : Curve} (u : HolomorphicMap D B) (hu : Nonconstant u)
    (hB : B.Hyperbolic) : D.Hyperbolic := by
  let hr := maps.ramification_finite D B u hu
  have hnegative := negative_cone_euler maps u hu hB hr
  have hnonnegative := divisorDegree_nonnegative (ramificationDivisor u hr)
  have hgenus : (1 : ℝ) < (D.genus : ℝ) := by
    unfold eulerCharacteristic at hnegative
    linarith
  have hnat : 1 < D.genus := by exact_mod_cast hgenus
  exact Nat.succ_le_iff.mpr hnat

/-- Equality of the actual derivative-zero orders gives equality of the
effective divisors. The finiteness proofs do not affect this conclusion. -/
theorem same_ramification_divisor {D B C : Curve}
    (u : HolomorphicMap D B) (v : HolomorphicMap D C)
    (hu : RamificationSupportFinite u) (hv : RamificationSupportFinite v)
    (hR : ∀ p, ramificationOrder u p = ramificationOrder v p) :
    ramificationDivisor u hu = ramificationDivisor v hv := by
  ext p
  exact hR p

/-- The metric-equality conclusion of Lemma 2.3, proved relative to the
separate, general classical inputs above. Only one hyperbolic target is
needed for the negative Euler-number check; both supplied target metrics
are smooth and have curvature -1. -/
theorem pullback_metrics_equal (maps : ClassicalCurveMapFacts)
    (pullbacks : ClassicalPullbackFacts) (unique : TroyanovUniqueness)
    {D B C : Curve} (u : HolomorphicMap D B) (v : HolomorphicMap D C)
    (hu : Nonconstant u) (hv : Nonconstant v) (hB : B.Hyperbolic)
    (gB : ConformalMetric B) (gC : ConformalMetric C)
    (hBcone : HasConeData gB 0) (hCcone : HasConeData gC 0)
    (hBcurv : HasConstantCurvature gB 0 (-1))
    (hCcurv : HasConstantCurvature gC 0 (-1))
    (hR : ∀ p, ramificationOrder u p = ramificationOrder v p) :
    pullback u gB = pullback v gC := by
  let hru := maps.ramification_finite D B u hu
  let hrv := maps.ramification_finite D C v hv
  have heq := same_ramification_divisor u v hru hrv hR
  apply unique D (ramificationDivisor u hru)
  · exact negative_cone_euler maps u hu hB hru
  · exact pullbacks.cone_data D B u hu hru gB hBcone
  · rw [heq]
    exact pullbacks.cone_data D C v hv hrv gC hCcone
  · exact pullbacks.curvature D B u hu hru gB hBcone hBcurv
  · rw [heq]
    exact pullbacks.curvature D C v hv hrv gC hCcone hCcurv

/-- On a regular germ, the candidate graph map is the second map composed
with a local inverse of the first. This is an identity of actual functions;
the construction/continuation of a hyperbolic local isometry is separate. -/
theorem graph_germ_of_local_inverse {u v i : ℂ → ℂ} {p : ℂ}
    (hinverse : i ∘ u =ᶠ[𝓝 p] id) :
    v =ᶠ[𝓝 p] (v ∘ i) ∘ u := by
  filter_upwards [hinverse] with z hz
  exact (congrArg v hz).symm

/-- The identity-theorem part of the graph assertion, including a ramified
centre: if the coordinate graph identity holds on a regular germ in a
connected neighbourhood and both sides are analytic on that neighbourhood,
it holds at every point, in particular at the ramified centre. Constructing
the local isometry from its first jet remains a separate geometric step. -/
theorem graph_identity_extension {U : Set ℂ} {u v φ : ℂ → ℂ}
    (hu : AnalyticOnNhd ℂ (φ ∘ u) U) (hv : AnalyticOnNhd ℂ v U)
    (hU : IsPreconnected U) {regular centre : ℂ} (hr : regular ∈ U)
    (hc : centre ∈ U) (hgerm : v =ᶠ[𝓝 regular] φ ∘ u) :
    v centre = φ (u centre) := by
  exact hv.eqOn_of_preconnected_of_eventuallyEq hu hU hr hgerm hc

end Paper27.Geometry.MetricComparison
