import Paper28.FiniteSphericalTriangulation
import Paper28.IntrinsicPolyhedralApproximation
import Mathlib.Algebra.Group.Subgroup.Finsupp

/-! Classical simultaneous geometric subdivision, with canonical simplex
integration additivity. The input refines only a finite list of actual
geodesic simplices and gives their finite signed characteristic-simplex
representations. It supplies no cycle, homology, filling or mass claim.
Finite integer assembly of the given current is a native proof below. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Set
variable {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
  {Y : Type} [metricY : MetricSpace Y] (S : FiniteSphericalTriangulation K Y)

abbrev NondegenerateCellwiseSimplex (k : ℕ) :=
  {σ : CellwiseGeodesicParameterization S k // LinearIndependent ℝ σ.geometric.rawVertices}

theorem cellwise_polyhedral_finite_sum
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) {k : ℕ} (Z : J.Current k)
    (hZ : Z ∈ cellwiseSphericalPolyhedralCurrents S A k) :
    ∃ F : Finset (NondegenerateCellwiseSimplex S k), ∃ a : F → ℤ,
      Z = ∑ σ : F, a σ • A.integration k σ.val.val.geometric.parameter := by
  classical
  obtain ⟨a,ha⟩ := AddSubgroup.exists_finsupp_of_mem_closure_range
    (fun σ : NondegenerateCellwiseSimplex S k => A.integration k σ.val.geometric.parameter) Z hZ
  refine ⟨a.support,fun σ => a σ.val,?_⟩
  rw [ha]
  exact (Finset.sum_attach a.support (fun σ => a σ • A.integration k σ.val.geometric.parameter)).symm

structure SphericalFiniteRefinementInput : Prop where
  refinement : ∀ {d : ℕ} {K : FiniteEuclideanComplex (EuclideanAmbient d)}
    {Y : Type} [metricY : MetricSpace Y] (S : FiniteSphericalTriangulation K Y),
    IntrinsicSphericalTriangulationMetric S → ∀ (y₀ : Y)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (A : LipschitzSimplexIntegrationInput metricY J) (k : ℕ)
    (F : Finset (NondegenerateCellwiseSimplex S k)),
    ∃ e : ℕ, ∃ K₁ : FiniteEuclideanComplex (EuclideanAmbient e),
    ∃ N : SphericalNeighborhoodRealization S K₁,
    ∃ z : F → finiteSimplicialChains K₁ k,
      ∀ σ : F, (intrinsicCanonicalCurrentChainMap N.atlas N.charts N.metric y₀ A).f k (z σ) =
        A.integration k σ.val.val.geometric.parameter

include S in
theorem cellwise_polyhedral_simplicial_representation
    (Ref : SphericalFiniteRefinementInput) (hMetric : IntrinsicSphericalTriangulationMetric S) (y₀ : Y)
    {J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY}
    (A : LipschitzSimplexIntegrationInput metricY J) {k : ℕ}
    (Z : J.Current k) (hZ : Z ∈ cellwiseSphericalPolyhedralCurrents S A k) :
    ∃ e : ℕ, ∃ K₁ : FiniteEuclideanComplex (EuclideanAmbient e),
    ∃ N : SphericalNeighborhoodRealization S K₁, ∃ z : finiteSimplicialChains K₁ k,
      (intrinsicCanonicalCurrentChainMap N.atlas N.charts N.metric y₀ A).f k z = Z := by
  obtain ⟨F,a,ha⟩ := cellwise_polyhedral_finite_sum S A Z hZ
  obtain ⟨e,K₁,N,z,hz⟩ := Ref.refinement S hMetric y₀ J A k F
  refine ⟨e,K₁,N,∑ σ : F, a σ • z σ,?_⟩
  change ((intrinsicCanonicalCurrentChainMap N.atlas N.charts N.metric y₀ A).f k).hom _ = _
  rw [map_sum]
  simp_rw [map_zsmul,hz]
  exact ha.symm

end Paper28
