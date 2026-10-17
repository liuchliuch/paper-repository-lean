import Paper28.FiniteSphericalPolyhedronApproximation

/-! Original Lemma 5.2, on the actual independent finite spherical
polyhedron and actual finite integer spherical polyhedral current groups.
The positive current degree is written k+1. All approximation, sharp mass,
relative cycle and exact prescribed filling conclusions are native proofs
under the precisely disclosed standard geometric/current foundations. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter
open scoped Topology

theorem lemma_5_2
    {Y : Type} [metricY : MetricSpace Y] (P : FiniteSphericalPolyhedron Y)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
    (Jc : ∀ j : Fin P.componentCount, CompactIntegralCurrentAlgebraInput.{0,0} (P.component j) inferInstance)
    (D : ComponentCurrentDecompositionInput P J Jc)
    (A : ∀ j, LipschitzSimplexIntegrationInput inferInstance (Jc j))
    (Foundations : ∀ j {e : ℕ} (K₁ : FiniteEuclideanComplex (EuclideanAmbient e))
      (N : SphericalNeighborhoodRealization (P.triangulation j) K₁),
      Nonempty (SphericalPolyhedronCurrentFoundations N (P.point j) (Jc j) (A j)))
    (PL : SphericalFullNeighborhoodInput) (Ref : SphericalFiniteRefinementInput)
    (RS : ∀ j, LipschitzCurrentHomologyComparisonInput (Jc j) (A j))
    (SS : SimplicialSingularHomologyComparisonInput) (k : ℕ) :
    (∀ Z : J.Current (k+1), J.boundary k Z = 0 →
      ∃ Zi : ℕ → J.Current (k+1), ∃ Wi : ℕ → J.Current (k+2),
        (∀ i, Zi i ∈ finiteSphericalPolyhedralCurrents P D A (k+1)) ∧
        (∀ i, J.boundary k (Zi i) = 0) ∧
        (∀ i, Z-Zi i = J.boundary (k+1) (Wi i)) ∧
        Tendsto (fun i => J.mass (Wi i)) atTop (𝓝 0) ∧
        Tendsto (fun i => J.mass (Zi i)) atTop (𝓝 (J.mass Z))) ∧
    (∀ Z : J.Current (k+1), Z ∈ finiteSphericalPolyhedralCurrents P D A (k+1) →
      (∃ W : J.Current (k+2), J.boundary (k+1) W = Z) →
      ∃ Q : J.Current (k+2), Q ∈ finiteSphericalPolyhedralCurrents P D A (k+2) ∧
        J.boundary (k+1) Q = Z) := by
  constructor
  · exact fun Z hZ => finite_spherical_polyhedron_sharp_approximation P J Jc D A Foundations PL Z hZ
  · intro Z hPoly hBounds
    have hZ : J.boundary k Z = 0 := by
      obtain ⟨W,hW⟩ := hBounds
      rw [← hW,J.boundary_squared_zero]
    exact finite_spherical_polyhedron_prescribed_filling P J Jc D A Foundations Ref RS SS Z hPoly hZ hBounds

end Paper28
