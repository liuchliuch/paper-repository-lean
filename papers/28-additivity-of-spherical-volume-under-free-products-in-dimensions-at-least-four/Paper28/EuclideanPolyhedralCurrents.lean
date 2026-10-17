import Paper28.CompactCurrentAlgebraInput
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Convex.Hull
import Mathlib.Algebra.Group.Subgroup.Lattice

/-! Actual affine Euclidean simplex integration objects and the standard
Stokes input. Polyhedral currents are finite integer combinations, and
boundary closure follows by native subgroup induction. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
universe v

abbrev EuclideanAmbient (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev AffineSimplexVertices (d k : ℕ) := Fin (k+1) → EuclideanAmbient d

structure EuclideanSimplexIntegrationInput (d : ℕ)
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance) where
  integration : ∀ k, AffineSimplexVertices d k → I.Current k
  support_subset : ∀ k (σ : AffineSimplexVertices d k),
    I.support (integration k σ) ⊆ convexHull ℝ (Set.range σ)
  stokes : ∀ k (σ : AffineSimplexVertices d (k+1)),
    I.boundary k (integration (k+1) σ) =
      ∑ i : Fin (k+2), ((-1 : ℤ)^(i : ℕ)) • integration k (fun j => σ (i.succAbove j))

def euclideanPolyhedralCurrents {d : ℕ}
    {I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) : AddSubgroup (I.Current k) :=
  AddSubgroup.closure (Set.range (S.integration k))

theorem euclideanPolyhedral_boundary_mem {d : ℕ}
    {I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance}
    (S : EuclideanSimplexIntegrationInput d I) (k : ℕ) (C : I.Current (k+1))
    (hC : C ∈ euclideanPolyhedralCurrents S (k+1)) :
    I.boundary k C ∈ euclideanPolyhedralCurrents S k := by
  change C ∈ (euclideanPolyhedralCurrents S k).comap (I.boundary k)
  apply ((AddSubgroup.closure_le _).mpr ?_) hC
  rintro C ⟨σ,rfl⟩
  change I.boundary k (S.integration (k+1) σ) ∈ euclideanPolyhedralCurrents S k
  rw [S.stokes]
  apply AddSubgroup.sum_mem
  intro i _
  apply AddSubgroup.zsmul_mem
  exact AddSubgroup.subset_closure (Set.mem_range_self _)

end Paper28
