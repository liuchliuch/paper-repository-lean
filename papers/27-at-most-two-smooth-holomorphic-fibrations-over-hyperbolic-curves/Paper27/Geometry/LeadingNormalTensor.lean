import Paper27.Geometry.NormalDegreeInvariance

/-!
# The intrinsic normal tensor from arbitrary adapted normal frames

Canonical curve chart domains need not be simply connected. Consequently a
normal frame cannot in general be rescaled on a whole chart domain so that
its nth power equals the tangent frame. We retain the actual nonzero leading
coefficient in each frame. The raw coefficient identity gives a holomorphic
gauge from the nth normal tensor power to the tangent line. Thus the degree
and negative Hom conclusions do not depend on a global choice of nth roots.

This is an own algebraic/bundle consequence of raw leading jets. Existence of
those jets for actual maps is not asserted or made an external theorem here.
-/
noncomputable section
open scoped Manifold
open Polynomial
namespace Paper27.Geometry.LeadingNormalTensor

open NormalDegreeInvariance

/-- A general first-order normal coordinate change can have every higher
coefficient. Its nth power still has leading coefficient `λ^n`. -/
theorem first_order_power_leading (n : ℕ) (lam : ℂ) (H : ℂ[X]) :
    (NormalJets.normalChange 1 lam H ^ n).coeff n = lam ^ n := by
  rw [NormalJets.normalChange_power_coeff, if_pos le_rfl, Nat.sub_self]
  exact NormalJets.normalUnit_power_constant (by omega) n lam H

/-- Raw leading jets in arbitrary honest adapted frames. The local leading
coefficients need not be one. The raw identity is the degree-n coefficient
of the actual coordinate functional identity; its consequence is proved below.
This record is intermediate output data, not an external existence input. -/
structure LeadingJetData {X : CompactComplexSurface} (D : EmbeddedCurve X)
    (N : HolomorphicLineCocycle D.curve) (T : TangentLineCocycle D.curve)
    (n : ℕ) where
  leading : D.curve → D.curve → ℂ
  holomorphic : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (leading i)
    (D.curve.chartDomain i)
  nonzero : ∀ i p, p ∈ D.curve.chartDomain i → leading i p ≠ 0
  Y : D.curve → D.curve → D.curve → ℂ[X]
  H : D.curve → D.curve → D.curve → ℂ[X]
  first_order : ∀ i j p, p ∈ D.curve.chartDomain i → p ∈ D.curve.chartDomain j →
    Y i j p = NormalJets.normalChange 1 (N.transition i j p) (H i j p)
  raw_leading : ∀ i j p, p ∈ D.curve.chartDomain i → p ∈ D.curve.chartDomain j →
    (C (leading j p) * Y i j p ^ n).coeff n =
      D.curve.chartJacobian i j p * leading i p

namespace LeadingJetData
variable {X : CompactComplexSurface} {D : EmbeddedCurve X}
  {N : HolomorphicLineCocycle D.curve} {T : TangentLineCocycle D.curve} {n : ℕ}

theorem leading_transition (A : LeadingJetData D N T n) (i j p : D.curve)
    (hi : p ∈ D.curve.chartDomain i) (hj : p ∈ D.curve.chartDomain j) :
    A.leading j p * N.transition i j p ^ n = T.bundle.transition i j p * A.leading i p := by
  have h := A.raw_leading i j p hi hj
  rw [A.first_order i j p hi hj, coeff_C_mul, first_order_power_leading,
    ← T.transition_eq i j p hi hj] at h
  exact h

/-- The actual holomorphic isomorphism is constructed from the raw jets. -/
def normalTensorGauge (A : LeadingJetData D N T n) :
    HolomorphicLineGauge (N.tensorPower n) T.bundle where
  coefficient := A.leading
  holomorphic := A.holomorphic
  nonzero := A.nonzero
  compatible := A.leading_transition

theorem tensor_degree (A : LeadingJetData D N T n) (theory : LineBundleDegreeTheory)
    (invariance : LineBundleDegreeGaugeInvariance theory) :
    (n : ℤ) * theory.degree D.curve N = theory.degree D.curve T.bundle := by
  rw [← theory.tensor_power D.curve N n]
  exact invariance D.curve (N.tensorPower n) T.bundle A.normalTensorGauge

theorem normal_degree_negative (A : LeadingJetData D N T n)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (hn : 0 < n) (hD : D.curve.Hyperbolic) : theory.degree D.curve N < 0 := by
  have hdegree := A.tensor_degree theory invariance
  rw [theory.tangent_degree D.curve T] at hdegree
  have hD' : (2 : ℤ) ≤ D.curve.genus := by exact_mod_cast hD
  have hn' : (0 : ℤ) < n := by exact_mod_cast hn
  have hnegative : (n : ℤ) * theory.degree D.curve N < 0 := by omega
  by_contra h
  exact (not_lt_of_ge (mul_nonneg (le_of_lt hn') (le_of_not_gt h))) hnegative

theorem normal_hom_degree_negative (A : LeadingJetData D N T n)
    (theory : LineBundleDegreeTheory) (invariance : LineBundleDegreeGaugeInvariance theory)
    (homLaw : HomDegreeLaw theory) (hn : 2 ≤ n) (hD : D.curve.Hyperbolic)
    (H : HomLineCocycle N T.bundle) : theory.degree D.curve H.bundle < 0 :=
  normal_hom_degree theory homLaw D.curve N T.bundle H n hn
    (A.normal_degree_negative theory invariance (by omega) hD)
    (A.tensor_degree theory invariance)

end LeadingJetData

end Paper27.Geometry.LeadingNormalTensor
