import Paper27.Geometry.LineCocycles
import Paper27.Geometry.NormalJets

/-!
# The actual connection cocycle constructed in Appendix A

The input is the order-2n Taylor-jet identity of the three retractions under a
coordinate change. Equation (7) is *derived* with all intermediate coefficients
present. We then construct holomorphic local connection forms on the actual
curve, check their exact tangent-frame transformation law, and use the
explicit universal classical connection/degree theorem.
-/
noncomputable section
open scoped Manifold
open Polynomial
namespace Paper27.Geometry

/-- Finite Taylor data obtained by applying the ordinary Taylor/substitution
functor to the exact retraction coordinate identities. This structure contains
neither equation (7), a connection, a degree-zero result, nor an obstruction. -/
structure CompatibleRetractionJets (D : Curve) (T : TangentLineCocycle D)
    (n : ℕ) (a : ℂ) (b : D → D → ℂ) where
  jet : D → D → ℂ[X]
  remainder : D → D → D → ℂ[X]
  normalLinear : D → D → D → ℂ
  order_bound : ∀ i p, p ∈ D.chartDomain i → X ^ n ∣ jet i p
  leading : ∀ i p, p ∈ D.chartDomain i → (jet i p).coeff n = a
  double : ∀ i p, p ∈ D.chartDomain i → (jet i p).coeff (2 * n) = b i p
  normal_power_leading : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    normalLinear i j p ^ n = D.chartJacobian i j p
  normal_power_double : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    (NormalJets.normalChange n (normalLinear i j p) (remainder i j p) ^ n).coeff (2 * n) =
      D.coordinateDerivative i (T.bundle.transition i j) p / 2
  composition : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    ((jet j p).comp
      (NormalJets.normalChange n (normalLinear i j p) (remainder i j p))).coeff (2 * n) =
      (C (D.chartJacobian i j p) * jet i p +
        C (D.coordinateDerivative i (T.bundle.transition i j) p / 2) * jet i p ^ 2).coeff
          (2 * n)

namespace CompatibleRetractionJets

/-- The Appendix A coefficient comparison, including every intermediate term. -/
theorem equation_seven {D : Curve} {T : TangentLineCocycle D} {n : ℕ} {a : ℂ}
    {b : D → D → ℂ} (J : CompatibleRetractionJets D T n a b) (hn : 2 ≤ n)
    (i j p : D) (hi : p ∈ D.chartDomain i) (hj : p ∈ D.chartDomain j) :
    b j p * D.chartJacobian i j p ^ 2 =
      D.chartJacobian i j p * b i p + (a ^ 2 - a) / 2 *
        D.coordinateDerivative i (T.bundle.transition i j) p := by
  have h := NormalJets.equation_seven_from_jet_compatibility hn
    (J.jet i p) (J.jet j p) (J.remainder i j p) (J.normalLinear i j p) a
    (D.chartJacobian i j p) (D.coordinateDerivative i (T.bundle.transition i j) p)
    (J.order_bound i p hi) (J.order_bound j p hj)
    (J.leading i p hi) (J.leading j p hj)
    (J.normal_power_leading i j p hi hj) (J.normal_power_double i j p hi hj)
    (J.composition i j p hi hj)
  simpa only [J.double i p hi, J.double j p hj] using h

/-- The constructed local connection form Γ_i=-2b_i/(a²-a). -/
def gamma (a : ℂ) (b : D → D → ℂ) (i p : D) : ℂ := (-2 / (a ^ 2 - a)) * b i p

/-- The ordinary connection cocycle on TD is actually constructed from the jet
identity. It is not included in the geometric input. -/
def tangentConnection {D : Curve} {T : TangentLineCocycle D} {n : ℕ} {a : ℂ}
    {b : D → D → ℂ} (J : CompatibleRetractionJets D T n a b) (hn : 2 ≤ n)
    (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (hb : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b i) (D.chartDomain i)) :
    T.bundle.Connection where
  coefficient := gamma a b
  holomorphic i := by
    have hconst : MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
        (fun _ : D => -2 / (a ^ 2 - a)) (D.chartDomain i) := mdifferentiableOn_const
    exact hconst.mul (hb i)
  transformation i j p hi hj := by
    have hp : D.chartJacobian i j p ≠ 0 := by
      rw [← T.transition_eq i j p hi hj]
      exact T.bundle.nonzero i j p hi hj
    have hΓ := Paper27.JetCalculation.connection_coefficient_law a
      (D.chartJacobian i j p) (D.coordinateDerivative i (T.bundle.transition i j) p)
      (b i p) (b j p) ha0 ha1 (J.equation_seven hn i j p hi hj)
    have hΓ' : gamma a b j p * D.chartJacobian i j p ^ 2 =
        D.chartJacobian i j p * gamma a b i p -
          D.coordinateDerivative i (T.bundle.transition i j) p := by
      convert hΓ using 1 <;> unfold gamma <;> ring
    rw [T.transition_eq i j p hi hj]
    apply mul_right_cancel₀ hp
    calc
      gamma a b j p * D.chartJacobian i j p * D.chartJacobian i j p =
          gamma a b j p * D.chartJacobian i j p ^ 2 := by ring
      _ = D.chartJacobian i j p * gamma a b i p -
          D.coordinateDerivative i (T.bundle.transition i j) p := hΓ'
      _ = (gamma a b i p - D.coordinateDerivative i (T.bundle.transition i j) p /
          D.chartJacobian i j p) * D.chartJacobian i j p := by field_simp

/-- Appendix A's obstruction, relative only to the universal degree laws of
classical line-bundle theory and the honest Taylor data above. -/
theorem common_tangency_impossible (theory : LineBundleDegreeTheory)
    (D : Curve) (T : TangentLineCocycle D) (hg : D.Hyperbolic)
    (n : ℕ) (hn : 2 ≤ n) (a : ℂ) (ha0 : a ≠ 0) (ha1 : a ≠ 1)
    (b : D → D → ℂ)
    (hb : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (b i) (D.chartDomain i))
    (J : CompatibleRetractionJets D T n a b) : False := by
  have hz := theory.connection_degree_zero D T.bundle
    ⟨J.tangentConnection hn ha0 ha1 hb⟩
  have ht := theory.tangent_degree D T
  have hg' : (2 : ℤ) ≤ D.genus := by exact_mod_cast hg
  omega

end CompatibleRetractionJets
end Paper27.Geometry
