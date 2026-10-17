import Paper27.Geometry.RamificationCovectors
import Paper27.Geometry.MetricComparison
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Analytic unit gauges on a normalized ramification curve

The coefficient functions here are actual complex-valued functions. In the
application, `A₁,A₂` and `B₁,B₂` are the coefficients of `df` and `dg`, pulled
back to a normalization coordinate, and `t₁,t₂` are the two coordinate
derivatives of that normalization. The zero determinant and the two explicit
chain-rule identities suffice to construct the analytic unit relating the
restricted derivatives. The unit relation and equality of ramification orders
are conclusions, not assumptions.

`CurveCovectorData` records these raw local coefficients for the actual curve
maps and their actual written-coordinate derivatives. Producing this data from
the ambient surface, its ramification locus, and a normalization remains the
application's responsibility. The only additional classical input in the
constancy result is the general zero-differential constancy theorem, stated
for every holomorphic map of compact connected curves. Its converse and the
equivalence of constancy for the two actual maps are proved here.
-/

noncomputable section

open scoped Manifold Topology
open Filter

namespace Paper27.Geometry.CovectorGauges

private theorem analytic_unit_of_first_component_ne_zero
    {A₁ A₂ B₁ B₂ : ℂ → ℂ} {z₀ : ℂ}
    (hA₁ : AnalyticAt ℂ A₁ z₀) (hB₁ : AnalyticAt ℂ B₁ z₀)
    (hA : A₁ z₀ ≠ 0) (hB : B₁ z₀ ≠ 0 ∨ B₂ z₀ ≠ 0)
    (hdet : ∀ᶠ z in 𝓝 z₀, A₁ z * B₂ z = A₂ z * B₁ z) :
    ∃ unit : ℂ → ℂ, AnalyticAt ℂ unit z₀ ∧ unit z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, B₁ z = unit z * A₁ z ∧ B₂ z = unit z * A₂ z := by
  let unit : ℂ → ℂ := fun z => B₁ z / A₁ z
  have hu : AnalyticAt ℂ unit z₀ := hB₁.fun_div hA₁ hA
  have hcoeff : ∀ᶠ z in 𝓝 z₀,
      B₁ z = unit z * A₁ z ∧ B₂ z = unit z * A₂ z := by
    filter_upwards [hA₁.continuousAt.eventually_ne hA, hdet] with z hAz hdetz
    constructor
    · exact (div_mul_cancel₀ (B₁ z) hAz).symm
    · apply mul_left_cancel₀ hAz
      calc
        A₁ z * B₂ z = A₂ z * B₁ z := hdetz
        _ = A₁ z * (unit z * A₂ z) := by
          dsimp [unit]
          field_simp
  refine ⟨unit, hu, ?_, hcoeff⟩
  intro hzero
  have hcentre := hcoeff.self_of_nhds
  have hB₁zero : B₁ z₀ = 0 := by rw [hcentre.1, hzero, zero_mul]
  have hB₂zero : B₂ z₀ = 0 := by rw [hcentre.2, hzero, zero_mul]
  exact hB.elim (fun h => h hB₁zero) (fun h => h hB₂zero)

/-- Two nonzero analytic covector pairs with zero determinant along the
normalization are related by an analytic unit germ. The gauge is constructed
as the quotient in a component nonzero at the centre. -/
theorem analytic_unit_of_zero_determinant
    {A₁ A₂ B₁ B₂ : ℂ → ℂ} {z₀ : ℂ}
    (hA₁ : AnalyticAt ℂ A₁ z₀) (hA₂ : AnalyticAt ℂ A₂ z₀)
    (hB₁ : AnalyticAt ℂ B₁ z₀) (hB₂ : AnalyticAt ℂ B₂ z₀)
    (hA : A₁ z₀ ≠ 0 ∨ A₂ z₀ ≠ 0) (hB : B₁ z₀ ≠ 0 ∨ B₂ z₀ ≠ 0)
    (hdet : ∀ᶠ z in 𝓝 z₀, A₁ z * B₂ z = A₂ z * B₁ z) :
    ∃ unit : ℂ → ℂ, AnalyticAt ℂ unit z₀ ∧ unit z₀ ≠ 0 ∧
      ∀ᶠ z in 𝓝 z₀, B₁ z = unit z * A₁ z ∧ B₂ z = unit z * A₂ z := by
  rcases hA with hA | hA
  · exact analytic_unit_of_first_component_ne_zero hA₁ hB₁ hA hB hdet
  · have hdet' : ∀ᶠ z in 𝓝 z₀, A₂ z * B₁ z = A₁ z * B₂ z :=
      hdet.mono fun _ h => h.symm
    obtain ⟨unit, hu, hu0, hcoeff⟩ :=
      analytic_unit_of_first_component_ne_zero hA₂ hB₂ hA hB.symm hdet'
    exact ⟨unit, hu, hu0, hcoeff.mono fun _ h => h.symm⟩

/-- Combining the constructed covector gauge with the actual derivative
chain rules gives a unit relation between actual scalar derivatives. No
nonvanishing of the normalization derivative `t₁,t₂` is required. -/
theorem derivative_unit_germ
    {A₁ A₂ B₁ B₂ t₁ t₂ u v : ℂ → ℂ} {z₀ : ℂ}
    (hA₁ : AnalyticAt ℂ A₁ z₀) (hA₂ : AnalyticAt ℂ A₂ z₀)
    (hB₁ : AnalyticAt ℂ B₁ z₀) (hB₂ : AnalyticAt ℂ B₂ z₀)
    (hA : A₁ z₀ ≠ 0 ∨ A₂ z₀ ≠ 0) (hB : B₁ z₀ ≠ 0 ∨ B₂ z₀ ≠ 0)
    (hdet : ∀ᶠ z in 𝓝 z₀, A₁ z * B₂ z = A₂ z * B₁ z)
    (hu : deriv u =ᶠ[𝓝 z₀] fun z => A₁ z * t₁ z + A₂ z * t₂ z)
    (hv : deriv v =ᶠ[𝓝 z₀] fun z => B₁ z * t₁ z + B₂ z * t₂ z) :
    ∃ unit : ℂ → ℂ, AnalyticAt ℂ unit z₀ ∧ unit z₀ ≠ 0 ∧
      deriv v =ᶠ[𝓝 z₀] unit * deriv u := by
  obtain ⟨unit, hunit, hunit0, hcoeff⟩ :=
    analytic_unit_of_zero_determinant hA₁ hA₂ hB₁ hB₂ hA hB hdet
  refine ⟨unit, hunit, hunit0, ?_⟩
  filter_upwards [hcoeff, hu, hv] with z hz huz hvz
  change deriv v z = unit z * deriv u z
  rw [hvz, huz, hz.1, hz.2]
  ring

/-- The actual derivative-zero orders agree. This invokes the previously
proved analytic-unit order lemma only after constructing its unit from raw
covector coefficients and chain rules. -/
theorem derivative_orders_equal_of_zero_determinant
    {A₁ A₂ B₁ B₂ t₁ t₂ u v : ℂ → ℂ} {z₀ : ℂ}
    (hA₁ : AnalyticAt ℂ A₁ z₀) (hA₂ : AnalyticAt ℂ A₂ z₀)
    (hB₁ : AnalyticAt ℂ B₁ z₀) (hB₂ : AnalyticAt ℂ B₂ z₀)
    (hA : A₁ z₀ ≠ 0 ∨ A₂ z₀ ≠ 0) (hB : B₁ z₀ ≠ 0 ∨ B₂ z₀ ≠ 0)
    (hdet : ∀ᶠ z in 𝓝 z₀, A₁ z * B₂ z = A₂ z * B₁ z)
    (hu : deriv u =ᶠ[𝓝 z₀] fun z => A₁ z * t₁ z + A₂ z * t₂ z)
    (hv : deriv v =ᶠ[𝓝 z₀] fun z => B₁ z * t₁ z + B₂ z * t₂ z)
    (hdu : AnalyticAt ℂ (deriv u) z₀) :
    analyticOrderNatAt (deriv v) z₀ = analyticOrderNatAt (deriv u) z₀ := by
  obtain ⟨unit, hunit, hunit0, hrel⟩ :=
    derivative_unit_germ hA₁ hA₂ hB₁ hB₂ hA hB hdet hu hv
  exact RamificationCovectors.derivative_orders_eq_of_unit_relation hunit hdu hunit0 hrel

/-- Raw analytic coefficient data for actual maps on a curve. In the
normalization application, the component functions are the pulled-back
ambient covector components and `t₁,t₂` are the normalization derivatives.
In particular, no global unit or common ramification divisor is a field. -/
structure CurveCovectorData {D B C : Curve}
    (u : HolomorphicMap D B) (v : HolomorphicMap D C) where
  A₁ : D → ℂ → ℂ
  A₂ : D → ℂ → ℂ
  B₁ : D → ℂ → ℂ
  B₂ : D → ℂ → ℂ
  t₁ : D → ℂ → ℂ
  t₂ : D → ℂ → ℂ
  analytic_A₁ : ∀ p : D, AnalyticAt ℂ (A₁ p) (chartAt ℂ p p)
  analytic_A₂ : ∀ p : D, AnalyticAt ℂ (A₂ p) (chartAt ℂ p p)
  analytic_B₁ : ∀ p : D, AnalyticAt ℂ (B₁ p) (chartAt ℂ p p)
  analytic_B₂ : ∀ p : D, AnalyticAt ℂ (B₂ p) (chartAt ℂ p p)
  nonzero_A : ∀ p : D, A₁ p (chartAt ℂ p p) ≠ 0 ∨ A₂ p (chartAt ℂ p p) ≠ 0
  nonzero_B : ∀ p : D, B₁ p (chartAt ℂ p p) ≠ 0 ∨ B₂ p (chartAt ℂ p p) ≠ 0
  determinant_zero : ∀ p : D, ∀ᶠ z in 𝓝 (chartAt ℂ p p),
    A₁ p z * B₂ p z = A₂ p z * B₁ p z
  chain_u : ∀ p : D, deriv (MetricComparison.writtenCoordinateMap u p) =ᶠ[𝓝 (chartAt ℂ p p)]
    fun z => A₁ p z * t₁ p z + A₂ p z * t₂ p z
  chain_v : ∀ p : D, deriv (MetricComparison.writtenCoordinateMap v p) =ᶠ[𝓝 (chartAt ℂ p p)]
    fun z => B₁ p z * t₁ p z + B₂ p z * t₂ p z

namespace CurveCovectorData

variable {D B C : Curve} {u : HolomorphicMap D B} {v : HolomorphicMap D C}

theorem unit_germ (data : CurveCovectorData u v) (p : D) :
    ∃ unit : ℂ → ℂ, AnalyticAt ℂ unit (chartAt ℂ p p) ∧ unit (chartAt ℂ p p) ≠ 0 ∧
      deriv (MetricComparison.writtenCoordinateMap v p) =ᶠ[𝓝 (chartAt ℂ p p)]
        unit * deriv (MetricComparison.writtenCoordinateMap u p) :=
  derivative_unit_germ (data.analytic_A₁ p) (data.analytic_A₂ p)
    (data.analytic_B₁ p) (data.analytic_B₂ p) (data.nonzero_A p) (data.nonzero_B p)
    (data.determinant_zero p) (data.chain_u p) (data.chain_v p)

theorem ramification_orders_equal (data : CurveCovectorData u v)
    (hdu : ∀ p, AnalyticAt ℂ (deriv (MetricComparison.writtenCoordinateMap u p))
      (chartAt ℂ p p)) :
    ∀ p, MetricComparison.ramificationOrder v p = MetricComparison.ramificationOrder u p := by
  intro p
  exact derivative_orders_equal_of_zero_determinant
    (data.analytic_A₁ p) (data.analytic_A₂ p) (data.analytic_B₁ p) (data.analytic_B₂ p)
    (data.nonzero_A p) (data.nonzero_B p) (data.determinant_zero p)
    (data.chain_u p) (data.chain_v p) (hdu p)

end CurveCovectorData

def IsConstant {D B : Curve} (u : HolomorphicMap D B) : Prop :=
  ∃ b : B, ∀ p : D, u p = b

/-- The universal connected zero-differential constancy theorem. It contains
no assertion about two maps, ramification, or Proposition 2.4. Its local
complex-analytic content is the usual zero derivative constancy theorem;
connectedness then gives a single global value. A published differential
geometric source is R. L. Fernandes, *Lectures on Differential Geometry*,
World Scientific (2024), Proposition 6.2, p. 48, DOI 10.1142/12733:
zero differential on a connected open set implies constancy there. The
interface uses the complex-coordinate form of that general statement. -/
def ClassicalZeroDifferentialConstancy : Prop :=
  ∀ (D B : Curve) (u : HolomorphicMap D B),
    (∀ p, deriv (MetricComparison.writtenCoordinateMap u p) (chartAt ℂ p p) = 0) →
      IsConstant u

/-- The converse direction needs no external theorem: a globally constant
actual map has globally constant written-coordinate functions. -/
theorem coordinate_derivative_zero_of_constant {D B : Curve}
    (u : HolomorphicMap D B) (hu : IsConstant u) (p : D) :
    deriv (MetricComparison.writtenCoordinateMap u p) (chartAt ℂ p p) = 0 := by
  obtain ⟨b, hb⟩ := hu
  have hcoord : MetricComparison.writtenCoordinateMap u p =
      fun _ : ℂ => chartAt ℂ (u p) b := by
    funext z
    exact congrArg (chartAt ℂ (u p)) (hb ((chartAt ℂ p).symm z))
  rw [hcoord]
  simp

/-- Pointwise unit germs imply equivalence of actual zero differentials,
even at singular points of the normalization map. -/
theorem CurveCovectorData.coordinate_derivative_zero_iff
    {D B C : Curve} {u : HolomorphicMap D B} {v : HolomorphicMap D C}
    (data : CurveCovectorData u v) (p : D) :
    deriv (MetricComparison.writtenCoordinateMap u p) (chartAt ℂ p p) = 0 ↔
      deriv (MetricComparison.writtenCoordinateMap v p) (chartAt ℂ p p) = 0 := by
  obtain ⟨unit, _, hunit0, hrel⟩ := data.unit_germ p
  have hc := hrel.self_of_nhds
  change deriv (MetricComparison.writtenCoordinateMap v p) (chartAt ℂ p p) =
    unit (chartAt ℂ p p) *
      deriv (MetricComparison.writtenCoordinateMap u p) (chartAt ℂ p p) at hc
  rw [hc, mul_eq_zero]
  simp [hunit0]

/-- The two actual restricted maps are constant together. The analytic unit
is constructed from the coefficient data at each point; neither simultaneous
nonconstancy nor a supplied unit relation is assumed. -/
theorem CurveCovectorData.constant_iff (constant : ClassicalZeroDifferentialConstancy)
    {D B C : Curve} {u : HolomorphicMap D B} {v : HolomorphicMap D C}
    (data : CurveCovectorData u v) : IsConstant u ↔ IsConstant v := by
  constructor
  · intro hu
    apply constant D C v
    intro p
    exact (data.coordinate_derivative_zero_iff p).mp
      (coordinate_derivative_zero_of_constant u hu p)
  · intro hv
    apply constant D B u
    intro p
    exact (data.coordinate_derivative_zero_iff p).mpr
      (coordinate_derivative_zero_of_constant v hv p)

theorem nonconstant_iff_not_constant {D B : Curve} (u : HolomorphicMap D B) :
    MetricComparison.Nonconstant u ↔ ¬ IsConstant u := by
  constructor
  · rintro ⟨p, q, hpq⟩ ⟨b, hb⟩
    exact hpq ((hb p).trans (hb q).symm)
  · intro hnot
    by_contra hn
    apply hnot
    refine ⟨u D.basepoint, fun p => ?_⟩
    by_contra hp
    exact hn ⟨p, D.basepoint, hp⟩

theorem CurveCovectorData.nonconstant_iff (constant : ClassicalZeroDifferentialConstancy)
    {D B C : Curve} {u : HolomorphicMap D B} {v : HolomorphicMap D C}
    (data : CurveCovectorData u v) :
    MetricComparison.Nonconstant u ↔ MetricComparison.Nonconstant v := by
  rw [nonconstant_iff_not_constant, nonconstant_iff_not_constant, data.constant_iff constant]

/-- The earlier finite-pair argument supplies at least one nonconstant
projection. The constructed gauges then give both nonconstant projections. -/
theorem CurveCovectorData.both_nonconstant (constant : ClassicalZeroDifferentialConstancy)
    {D B C : Curve} {u : HolomorphicMap D B} {v : HolomorphicMap D C}
    (data : CurveCovectorData u v)
    (hone : MetricComparison.Nonconstant u ∨ MetricComparison.Nonconstant v) :
    MetricComparison.Nonconstant u ∧ MetricComparison.Nonconstant v := by
  rcases hone with hu | hv
  · exact ⟨hu, (data.nonconstant_iff constant).mp hu⟩
  · exact ⟨(data.nonconstant_iff constant).mpr hv, hv⟩

/-- The normalization argument's combined output: one nonconstant
projection and the raw covector data give two nonconstant projections and
equality of their actual derivative-zero orders. The analyticity input is
the universal curve-map fact, applied only after nonconstancy is proved. -/
theorem CurveCovectorData.nonconstant_and_same_ramification
    (maps : MetricComparison.ClassicalCurveMapFacts)
    (constant : ClassicalZeroDifferentialConstancy)
    {D B C : Curve} {u : HolomorphicMap D B} {v : HolomorphicMap D C}
    (data : CurveCovectorData u v)
    (hone : MetricComparison.Nonconstant u ∨ MetricComparison.Nonconstant v) :
    MetricComparison.Nonconstant u ∧ MetricComparison.Nonconstant v ∧
      ∀ p, MetricComparison.ramificationOrder u p = MetricComparison.ramificationOrder v p := by
  obtain ⟨hu, hv⟩ := data.both_nonconstant constant hone
  exact ⟨hu, hv, fun p =>
    (data.ramification_orders_equal (maps.derivative_analytic D B u hu) p).symm⟩

end Paper27.Geometry.CovectorGauges
