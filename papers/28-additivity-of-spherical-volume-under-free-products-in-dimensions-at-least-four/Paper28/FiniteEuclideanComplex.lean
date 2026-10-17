import Mathlib.Analysis.Convex.SimplicialComplex.Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Analysis.Normed.Module.Convex

/-! Native finite Euclidean polyhedra, with compactness and completeness
of their actual underlying simplicial-complex subspaces. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]

structure FiniteEuclideanComplex (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H] where
  complex : Geometry.SimplicialComplex ℝ H
  finite_faces : complex.faces.Finite

theorem FiniteEuclideanComplex.isCompact_space (K : FiniteEuclideanComplex H) : IsCompact K.complex.space := by
  exact K.finite_faces.isCompact_biUnion (fun s _ => s.finite_toSet.isCompact_convexHull)

instance FiniteEuclideanComplex.compactSpace (K : FiniteEuclideanComplex H) : CompactSpace K.complex.space :=
  isCompact_iff_compactSpace.mp K.isCompact_space

instance FiniteEuclideanComplex.completeSpace (K : FiniteEuclideanComplex H) : CompleteSpace K.complex.space :=
  completeSpace_coe_iff_isComplete.mpr K.isCompact_space.isComplete

end Paper28
