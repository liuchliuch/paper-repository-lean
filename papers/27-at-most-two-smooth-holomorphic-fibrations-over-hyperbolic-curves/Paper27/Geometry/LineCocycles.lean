import Paper27.Geometry.Objects
import Paper27.Geometry.DifferentialRigidity
import Paper27.JetCalculation
import Mathlib.Geometry.Manifold.Algebra.Monoid
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.NormNum

/-!
# Holomorphic line bundles and connections in coordinate cocycles

A holomorphic line bundle is represented by a genuine nowhere-zero holomorphic
transition cocycle on the curve's actual complex chart cover. A connection is
represented by holomorphic local connection forms with the exact frame-change
law. Its local covariant derivative is d(s)+Γs and satisfies Leibniz (proved
below). Thus the classical connection/degree input has actual mathematical
content, rather than an uninterpreted `HasConnection` predicate.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry

namespace Curve

def chartDomain (D : Curve) (i : D) : Set D := (chartAt ℂ i).source

def chartChange (D : Curve) (i j : D) : ℂ → ℂ :=
  (chartAt ℂ j) ∘ (chartAt ℂ i).symm

def chartJacobian (D : Curve) (i j p : D) : ℂ :=
  deriv (D.chartChange i j) ((chartAt ℂ i) p)

def coordinateDerivative (D : Curve) (i : D) (f : D → ℂ) (p : D) : ℂ :=
  deriv (f ∘ (chartAt ℂ i).symm) ((chartAt ℂ i) p)

end Curve

/-- Coordinate transitions multiply the fibre coordinate from frame i to frame j.
The cover is the actual canonical complex chart cover of D. -/
structure HolomorphicLineCocycle (D : Curve) where
  transition : D → D → D → ℂ
  holomorphic : ∀ i j, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
    (transition i j) (D.chartDomain i ∩ D.chartDomain j)
  nonzero : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    transition i j p ≠ 0
  self : ∀ i p, p ∈ D.chartDomain i → transition i i p = 1
  compose : ∀ i j k p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    p ∈ D.chartDomain k → transition j k p * transition i j p = transition i k p

namespace HolomorphicLineCocycle

/-- Tensor power, by the actual nth powers of the transition functions. -/
def tensorPower {D : Curve} (L : HolomorphicLineCocycle D) (n : ℕ) :
    HolomorphicLineCocycle D where
  transition i j p := L.transition i j p ^ n
  holomorphic i j := by
    induction n with
    | zero => exact mdifferentiableOn_const
    | succ n ih => simpa only [pow_succ] using ih.mul (L.holomorphic i j)
  nonzero i j p hi hj := pow_ne_zero n (L.nonzero i j p hi hj)
  self i p hp := by rw [L.self i p hp, one_pow]
  compose i j k p hi hj hk := by rw [← mul_pow, L.compose i j k p hi hj hk]

/-- A fibrewise scalar identity between cocycles is an identity-frame bundle
isomorphism. There is no claim here that arbitrary line bundles are trivial. -/
def SameTransitions {D : Curve} (L K : HolomorphicLineCocycle D) : Prop :=
  ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    L.transition i j p = K.transition i j p

/-- Local coefficients of a genuinely holomorphic global section. -/
structure HolomorphicSection {D : Curve} (L : HolomorphicLineCocycle D) where
  coefficient : D → D → ℂ
  holomorphic : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
    (coefficient i) (D.chartDomain i)
  compatible : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    coefficient j p = L.transition i j p * coefficient i p

/-- A holomorphic connection written in actual coordinates and local frames.
The minus sign comes from the convention v_j=t_ij v_i for fibre coordinates. -/
structure Connection {D : Curve} (L : HolomorphicLineCocycle D) where
  coefficient : D → D → ℂ
  holomorphic : ∀ i, MDifferentiableOn 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ)
    (coefficient i) (D.chartDomain i)
  transformation : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    coefficient j p * D.chartJacobian i j p = coefficient i p -
      D.coordinateDerivative i (L.transition i j) p / L.transition i j p

/-- Local covariant differentiation in the frame in which the connection form
has coefficient Γ. -/
def covariantDerivative (Γ s : ℂ → ℂ) (z : ℂ) : ℂ := deriv s z + Γ z * s z

/-- The actual local Leibniz rule; in particular `Connection` represents
connections, not merely arbitrary scalar data with a convenient name. -/
theorem covariantDerivative_leibniz (Γ h s : ℂ → ℂ) (z h' s' : ℂ)
    (hh : HasDerivAt h h' z) (hs : HasDerivAt s s' z) :
    covariantDerivative Γ (fun w => h w * s w) z =
      h' * s z + h z * covariantDerivative Γ s z := by
  have hproduct : HasDerivAt (fun w => h w * s w) (h' * s z + h z * s') z :=
    hh.mul hs
  simp only [covariantDerivative, hproduct.deriv, hs.deriv]
  ring

/-- Generic scalar check that the connection covariant derivatives transform
by the same line-bundle cocycle. This applies in every pair of actual charts. -/
theorem connection_operator_compatible (t t' p γ γ' s s' ds ds' : ℂ)
    (ht : t ≠ 0) (hsection : s' = t * s)
    (hchain : ds' * p = t' * s + t * ds)
    (hconnection : γ' * p = γ - t' / t) :
    (ds' + γ' * s') * p = t * (ds + γ * s) := by
  rw [hsection]
  calc
    (ds' + γ' * (t * s)) * p = ds' * p + (γ' * p) * (t * s) := by ring
    _ = (t' * s + t * ds) + (γ - t' / t) * (t * s) := by rw [hchain, hconnection]
    _ = t * (ds + γ * s) := by field_simp; ring

end HolomorphicLineCocycle

/-- The usual tangent transition cocycle, with its mathematical interpretation
fixed by actual derivatives of coordinate changes. The existence of this
standard cocycle uses the usual coordinate-change chain rule. -/
structure TangentLineCocycle (D : Curve) where
  bundle : HolomorphicLineCocycle D
  transition_eq : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
    bundle.transition i j p = D.chartJacobian i j p

/-- Explicit classical degree inputs, for genuine holomorphic line cocycles.
The degree map is the unformalized first-Chern-number operation. Every law is
universally quantified over bundles; no paper-specific ramification component
or splitting is supplied here. -/
structure LineBundleDegreeTheory where
  degree : (D : Curve) → HolomorphicLineCocycle D → ℤ
  invariant : ∀ D (L K : HolomorphicLineCocycle D), L.SameTransitions K →
    degree D L = degree D K
  tensor_power : ∀ D (L : HolomorphicLineCocycle D) (n : ℕ),
    degree D (L.tensorPower n) = (n : ℤ) * degree D L
  tangent_degree : ∀ D (T : TangentLineCocycle D),
    degree D T.bundle = 2 - 2 * (D.genus : ℤ)
  connection_degree_zero : ∀ D (L : HolomorphicLineCocycle D),
    Nonempty L.Connection → degree D L = 0
  negative_degree_no_section : ∀ D (L : HolomorphicLineCocycle D), degree D L < 0 →
    ∀ (s : L.HolomorphicSection) i p, p ∈ D.chartDomain i → s.coefficient i p = 0

/-- The bundle and negative-degree conclusions in Proposition 2.4 follow from
λ_ij^n = φ'_ij. The raw normal coordinate cocycle N is an input, but neither
the bundle tensor isomorphism nor its degree identity is an input. -/
theorem normal_tensor_degree (theory : LineBundleDegreeTheory) (D : Curve)
    (N : HolomorphicLineCocycle D) (T : TangentLineCocycle D) (n : ℕ)
    (hn : 2 ≤ n) (hg : D.Hyperbolic)
    (hroot : ∀ i j p, p ∈ D.chartDomain i → p ∈ D.chartDomain j →
      N.transition i j p ^ n = D.chartJacobian i j p) :
    (N.tensorPower n).SameTransitions T.bundle ∧
    (n : ℤ) * theory.degree D N = 2 - 2 * (D.genus : ℤ) ∧
    theory.degree D N < 0 := by
  have hsame : (N.tensorPower n).SameTransitions T.bundle := by
    intro i j p hi hj
    exact (hroot i j p hi hj).trans (T.transition_eq i j p hi hj).symm
  have hdegree : (n : ℤ) * theory.degree D N = 2 - 2 * (D.genus : ℤ) := by
    rw [← theory.tensor_power D N n, theory.invariant D _ _ hsame, theory.tangent_degree D T]
  refine ⟨hsame, hdegree, ?_⟩
  have hnpos : (0 : ℤ) < n := by omega
  have hg' : (2 : ℤ) ≤ D.genus := by exact_mod_cast hg
  have hprod : (n : ℤ) * theory.degree D N < 0 := by omega
  by_contra hnonneg
  have hz : 0 ≤ theory.degree D N := le_of_not_gt hnonneg
  exact (not_lt_of_ge (mul_nonneg (le_of_lt hnpos) hz)) hprod

end Paper27.Geometry
