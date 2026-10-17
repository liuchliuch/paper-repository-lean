import Paper27.Geometry.SmoothCurveDecomposition
import Mathlib.Topology.LocallyConstant.Basic

/-!
# A uniform ramification index along an actual connected component

Local cyclic charts are intermediate output of the normalized branch
argument. The universal classical input is only local topological degree for
finite holomorphic maps and its value in actual cyclic coordinates. It has
no assertion of constancy on a critical component. That constancy follows
below from the actual open charts and connectedness of the actual curve.

Source for local multiplicity/topological degree: Dinh--Sibony, *Dynamics in
several complex variables*, Appendix A.1, pp.116--117, following Theorem A.1.3,
https://arxiv.org/abs/0810.0811 . Its value for `(x,y) ↦ (x,φ(x)+y^n)` is the
usual one-variable local degree of `y^n`, unchanged by biholomorphic source
and target coordinates. No P27 geometry is supplied by this interface.
-/
noncomputable section
open scoped Manifold
namespace Paper27.Geometry.RamificationIndexConstancy

open RamificationSupport SmoothCurveDecomposition

def criticalSet {X Y : CompactComplexSurface} (q : FiniteSurjectiveHolomorphicMap X Y) : Set X :=
  {x | ¬ Function.Surjective (mfderiv 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) q.map x)}

/-- Actual cyclic coordinates on an actual finite holomorphic map. The
critical-axis equality and exponent bound are proved when these data are
constructed; they are not part of any external existence theorem here. -/
structure SurfaceCyclicChart {X Y : CompactComplexSurface}
    (q : FiniteSurjectiveHolomorphicMap X Y) (p : X) where
  source : OpenPartialHomeomorph X (ℂ × ℂ)
  target : OpenPartialHomeomorph Y (ℂ × ℂ)
  source_mem : p ∈ source.source
  source_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) source source.source
  source_inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    source.symm source.target
  target_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) target target.source
  target_inverse_holomorphic : MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ)
    target.symm target.target
  maps_target : ∀ x ∈ source.source, q.map x ∈ target.source
  exponent : ℕ
  exponent_ge_two : 2 ≤ exponent
  graph : ℂ → ℂ
  graph_analytic : ∀ x ∈ source.source, AnalyticAt ℂ graph (source x).1
  identity : ∀ x ∈ source.source,
    target (q.map x) = localBranchMap exponent graph (source x)
  axis : ∀ x ∈ source.source, x ∈ criticalSet q ↔ (source x).2 = 0

def SurfaceCyclicChart.axisChart {X Y : CompactComplexSurface}
    {q : FiniteSurjectiveHolomorphicMap X Y} {p : X} (A : SurfaceCyclicChart q p) :
    HolomorphicAxisChart X (criticalSet q) p where
  coordinates := A.source
  centre_mem := A.source_mem
  holomorphic := A.source_holomorphic
  inverse_holomorphic := A.source_inverse_holomorphic
  axis := A.axis

/-- The general local-degree operation and the elementary cyclic-coordinate
computation. The law is quantified over arbitrary finite holomorphic maps,
actual biholomorphic charts and analytic graph functions. It supplies no
critical-set geometry, component, normal degree, or fibration conclusion. -/
structure FiniteLocalDegreeTheory where
  localDegree : ∀ (X Y : CompactComplexSurface), FiniteSurjectiveHolomorphicMap X Y → X → ℕ
  cyclic_coordinate_degree : ∀ (X Y : CompactComplexSurface)
    (q : FiniteSurjectiveHolomorphicMap X Y)
    (e : OpenPartialHomeomorph X (ℂ × ℂ)) (t : OpenPartialHomeomorph Y (ℂ × ℂ)),
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) e e.source →
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) e.symm e.target →
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) t t.source →
    MDifferentiableOn 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, ℂ × ℂ) t.symm t.target →
    (∀ x ∈ e.source, q.map x ∈ t.source) →
    ∀ (n : ℕ), 0 < n → ∀ (φ : ℂ → ℂ),
    (∀ x ∈ e.source, AnalyticAt ℂ φ (e x).1) →
    (∀ x ∈ e.source, t (q.map x) = localBranchMap n φ (e x)) →
    ∀ x ∈ e.source, (e x).2 = 0 → localDegree X Y q x = n

namespace SurfaceCyclicChart
variable {X Y : CompactComplexSurface} {q : FiniteSurjectiveHolomorphicMap X Y}
  {p : X}

theorem degree_at_critical (A : SurfaceCyclicChart q p) (degrees : FiniteLocalDegreeTheory)
    {x : X} (hx : x ∈ A.source.source) (hcritical : x ∈ criticalSet q) :
    degrees.localDegree X Y q x = A.exponent :=
  degrees.cyclic_coordinate_degree X Y q A.source A.target A.source_holomorphic
    A.source_inverse_holomorphic A.target_holomorphic A.target_inverse_holomorphic A.maps_target
    A.exponent (by have hn := A.exponent_ge_two; omega) A.graph A.graph_analytic A.identity
    x hx ((A.axis x hx).mp hcritical)

end SurfaceCyclicChart

/-- Connectedness turns the actual chart computations into one uniform
index on the component. This is the own component-constancy argument. -/
theorem component_index_constant (degrees : FiniteLocalDegreeTheory)
    {X Y : CompactComplexSurface} (q : FiniteSurjectiveHolomorphicMap X Y)
    (D : EmbeddedCurve X) (hD : D.support ⊆ criticalSet q)
    (charts : ∀ p ∈ criticalSet q, Nonempty (SurfaceCyclicChart q p)) :
    ∃ n : ℕ, 2 ≤ n ∧
      (∀ p : D.curve, degrees.localDegree X Y q (D.inclusion p) = n) ∧
      (∀ p : D.curve, ∀ A : SurfaceCyclicChart q (D.inclusion p), A.exponent = n) := by
  let index : D.curve → ℕ := fun p => degrees.localDegree X Y q (D.inclusion p)
  have hloc : IsLocallyConstant index := by
    apply (IsLocallyConstant.iff_exists_open index).mpr
    intro p
    obtain ⟨A⟩ := charts (D.inclusion p) (hD ⟨p, rfl⟩)
    refine ⟨D.inclusion ⁻¹' A.source.source,
      A.source.open_source.preimage D.inclusion.holomorphic.continuous, A.source_mem, ?_⟩
    intro s hs
    exact (A.degree_at_critical degrees hs (hD ⟨s, rfl⟩)).trans
      (A.degree_at_critical degrees A.source_mem (hD ⟨p, rfl⟩)).symm
  let p := D.curve.basepoint
  obtain ⟨A⟩ := charts (D.inclusion p) (hD ⟨p, rfl⟩)
  have hpdegree := A.degree_at_critical degrees A.source_mem (hD ⟨p, rfl⟩)
  refine ⟨index p, ?_, ?_, ?_⟩
  · change 2 ≤ degrees.localDegree X Y q (D.inclusion p)
    rw [hpdegree]
    exact A.exponent_ge_two
  · intro s
    exact hloc.apply_eq_of_preconnectedSpace s p
  · intro s B
    exact (B.degree_at_critical degrees B.source_mem (hD ⟨s, rfl⟩)).symm.trans
      (hloc.apply_eq_of_preconnectedSpace s p)

end Paper27.Geometry.RamificationIndexConstancy
