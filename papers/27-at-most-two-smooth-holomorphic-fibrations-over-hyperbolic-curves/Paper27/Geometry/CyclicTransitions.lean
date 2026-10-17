import Paper27.Geometry.Factorization
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Topology.Algebra.Field
import Mathlib.Tactic.FieldSimp

/-!
# Gluing the cyclic coordinate actions

This file proves the transition compatibility in Proposition 2.4, p.17. After
holomorphic division by the normal coordinate, a transition has the form y·h,
where h is a nowhere-zero continuous (in the source, holomorphic) unit. Its nth
power depends only on x and y^n. The quotient h(x,ζy)/h(x,y) takes values in a
finite root set and equals one on the fixed curve, so it equals one throughout
every connected overlap. No cyclic action on the surface is assumed here.
-/
noncomputable section
namespace Paper27.Geometry.CyclicTransitions

/-- A continuous family of nth roots of unity is constant on a connected space. -/
theorem root_valued_constant {U : Type*} [TopologicalSpace U] [PreconnectedSpace U]
    (n : ℕ) (hn : 0 < n) (q : U → ℂ) (hq : Continuous q)
    (hroot : ∀ u, q u ^ n = 1) (u₀ : U) (hq₀ : q u₀ = 1) : ∀ u, q u = 1 := by
  have hrange : (Set.range q).Finite := by
    apply (Polynomial.nthRootsFinset n (1 : ℂ)).finite_toSet.subset
    rintro _ ⟨u, rfl⟩
    exact (Polynomial.mem_nthRootsFinset hn 1).mpr (hroot u)
  have hconnected : IsPreconnected (Set.range q) := by
    simpa only [Set.image_univ] using isPreconnected_univ.image q hq.continuousOn
  have hsub := finite_preconnected_subsingleton hrange hconnected
  intro u
  exact (hsub ⟨u, rfl⟩ ⟨u₀, rfl⟩).trans hq₀

/-- Equality of the nth powers of a nowhere-zero unit, and a fixed point of the
normal rotation, force invariance of the unit itself on a connected overlap. -/
theorem unit_factor_invariant {U : Type*} [TopologicalSpace U] [PreconnectedSpace U]
    (n : ℕ) (hn : 0 < n) (τ : U → U) (hτ : Continuous τ)
    (h : U → ℂ) (hh : Continuous h) (hne : ∀ u, h u ≠ 0)
    (hpow : ∀ u, h (τ u) ^ n = h u ^ n)
    (u₀ : U) (hfixed : τ u₀ = u₀) : ∀ u, h (τ u) = h u := by
  have hqcont : Continuous (fun u => h (τ u) / h u) := (hh.comp hτ).div hh hne
  have hqpow : ∀ u, (h (τ u) / h u) ^ n = 1 := by
    intro u
    rw [div_pow, hpow u, div_self (pow_ne_zero _ (hne u))]
  have hq₀ : h (τ u₀) / h u₀ = 1 := by rw [hfixed, div_self (hne u₀)]
  have hall := root_valued_constant n hn _ hqcont hqpow u₀ hq₀
  intro u
  exact (div_eq_one_iff_eq (hne u)).mp (hall u)

/-- Consequently the source normal-coordinate transition y'=y·h commutes with
normal rotation by ζ. This is the compatibility needed for sheaf gluing of the
local automorphisms, independently of a choice of nth root of h^n. -/
theorem normal_transition_commutes {U : Type*} [TopologicalSpace U] [PreconnectedSpace U]
    (n : ℕ) (hn : 0 < n) (τ : U → U) (hτ : Continuous τ)
    (y h : U → ℂ) (hh : Continuous h) (hne : ∀ u, h u ≠ 0)
    (hpow : ∀ u, h (τ u) ^ n = h u ^ n)
    (u₀ : U) (hfixed : τ u₀ = u₀) (ζ : ℂ)
    (hy : ∀ u, y (τ u) = ζ * y u) :
    ∀ u, y (τ u) * h (τ u) = ζ * (y u * h u) := by
  intro u
  rw [unit_factor_invariant n hn τ hτ h hh hne hpow u₀ hfixed u, hy u, mul_assoc]

end Paper27.Geometry.CyclicTransitions
