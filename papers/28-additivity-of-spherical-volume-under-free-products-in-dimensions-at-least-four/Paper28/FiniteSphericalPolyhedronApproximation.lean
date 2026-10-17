import Paper28.FiniteSphericalComponents

/-! Native finite-component assembly of sharp approximation and exact
prescribed polyhedral filling. Only standard clopen current restriction /
canonical inclusion calculus is used in passing between components. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open CategoryTheory Filter Set
open scoped Topology
variable {Y : Type} [metricY : MetricSpace Y] (P : FiniteSphericalPolyhedron Y)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} Y metricY)
  (Jc : ∀ j : Fin P.componentCount, CompactIntegralCurrentAlgebraInput.{0,0} (P.component j) inferInstance)
  (D : ComponentCurrentDecompositionInput P J Jc)
  (A : ∀ j, LipschitzSimplexIntegrationInput inferInstance (Jc j))
  (Foundations : ∀ j {e : ℕ} (K₁ : FiniteEuclideanComplex (EuclideanAmbient e))
    (N : SphericalNeighborhoodRealization (P.triangulation j) K₁),
    Nonempty (SphericalPolyhedronCurrentFoundations N (P.point j) (Jc j) (A j)))

include Foundations in
theorem finite_spherical_polyhedron_sharp_approximation
    (PL : SphericalFullNeighborhoodInput) {k : ℕ} (Z : J.Current (k+1)) (hZ : J.boundary k Z = 0) :
    ∃ Zi : ℕ → J.Current (k+1), ∃ Wi : ℕ → J.Current (k+2),
      (∀ i, Zi i ∈ finiteSphericalPolyhedralCurrents P D A (k+1)) ∧
      (∀ i, J.boundary k (Zi i) = 0) ∧
      (∀ i, Z-Zi i = J.boundary (k+1) (Wi i)) ∧
      Tendsto (fun i => J.mass (Wi i)) atTop (𝓝 0) ∧
      Tendsto (fun i => J.mass (Zi i)) atTop (𝓝 (J.mass Z)) := by
  have hEach := fun j => connected_spherical_polyhedron_sharp_approximation
    (P.triangulation j) (P.point j) (A j) PL (P.metric j) (Foundations j) (D.restrict j (k+1) Z)
    (by
      have he := congrArg (D.restrict j k) hZ
      rw [D.restrict_boundary,map_zero] at he
      exact he)
  choose Q W hPoly hCy hHom hFill hMass using hEach
  let Zi : ℕ → J.Current (k+1) := fun i => ∑ j, componentPush P D j (k+1) (Q j i)
  let Wi : ℕ → J.Current (k+2) := fun i => ∑ j, componentPush P D j (k+2) (W j i)
  refine ⟨Zi,Wi,?_,?_,?_,?_,?_⟩
  · intro i
    exact AddSubgroup.sum_mem _ (fun j _ => component_polyhedral_push_mem P D A j (Q j i) (hPoly j i))
  · intro i
    change J.boundary k (∑ j, componentPush P D j (k+1) (Q j i)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro j _
    rw [componentPush_boundary,hCy j i,map_zero]
  · intro i
    change Z-(∑ j, componentPush P D j (k+1) (Q j i)) =
      J.boundary (k+1) (∑ j, componentPush P D j (k+2) (W j i))
    calc
      _ = ∑ j, (componentPush P D j (k+1) (D.restrict j (k+1) Z)-
          componentPush P D j (k+1) (Q j i)) := by
        have hr : Z = ∑ j, componentPush P D j (k+1) (D.restrict j (k+1) Z) := D.reconstruction _ Z
        simpa only [Finset.sum_sub_distrib] using
          congrArg (fun T => T-∑ j, componentPush P D j (k+1) (Q j i)) hr
      _ = ∑ j, J.boundary (k+1) (componentPush P D j (k+2) (W j i)) := by
        apply Finset.sum_congr rfl
        intro j _
        have he := congrArg (componentPush P D j (k+1)) (hHom j i)
        rw [map_sub] at he
        exact he.trans (componentPush_boundary P D j (k+1) (W j i)).symm
      _ = _ := (map_sum _ _ _).symm
  · have hfun : (fun i => J.mass (Wi i)) = fun i => ∑ j, (Jc j).mass (W j i) := by
      funext i
      exact D.mass_sum (k+2) (fun j => W j i)
    rw [hfun]
    simpa only [Finset.sum_const_zero] using (tendsto_finset_sum Finset.univ (fun j _ => hFill j))
  · have hfun : (fun i => J.mass (Zi i)) = fun i => ∑ j, (Jc j).mass (Q j i) := by
      funext i
      exact D.mass_sum (k+1) (fun j => Q j i)
    have hZM : J.mass Z = ∑ j, (Jc j).mass (D.restrict j (k+1) Z) :=
      (congrArg J.mass (D.reconstruction (k+1) Z)).trans (D.mass_sum _ _)
    rw [hfun,hZM]
    exact tendsto_finset_sum Finset.univ (fun j _ => hMass j)

include Foundations in
theorem finite_spherical_polyhedron_prescribed_filling
    (Ref : SphericalFiniteRefinementInput)
    (RS : ∀ j, LipschitzCurrentHomologyComparisonInput (Jc j) (A j))
    (SS : SimplicialSingularHomologyComparisonInput) {k : ℕ}
    (Z : J.Current (k+1)) (hPoly : Z ∈ finiteSphericalPolyhedralCurrents P D A (k+1))
    (hZ : J.boundary k Z = 0) (hBounds : ∃ W : J.Current (k+2), J.boundary (k+1) W = Z) :
    ∃ Q : J.Current (k+2), Q ∈ finiteSphericalPolyhedralCurrents P D A (k+2) ∧
      J.boundary (k+1) Q = Z := by
  obtain ⟨W,hW⟩ := hBounds
  have hEach := fun j => connected_spherical_polyhedron_prescribed_filling
    (P.triangulation j) (P.point j) (A j) Ref (P.metric j) (Foundations j) (RS j) SS
    (D.restrict j (k+1) Z) (component_restrict_polyhedral P D A j Z hPoly)
    (by
      have he := congrArg (D.restrict j k) hZ
      rw [D.restrict_boundary,map_zero] at he
      exact he)
    ⟨D.restrict j (k+2) W,(D.restrict_boundary j (k+1) W).symm.trans
      (congrArg (D.restrict j (k+1)) hW)⟩
  choose Q hQ hb using hEach
  refine ⟨∑ j, componentPush P D j (k+2) (Q j),?_,?_⟩
  · exact AddSubgroup.sum_mem _ (fun j _ => component_polyhedral_push_mem P D A j (Q j) (hQ j))
  · calc
      _ = ∑ j, componentPush P D j (k+1) (D.restrict j (k+1) Z) := by
        rw [map_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [componentPush_boundary,hb j]
      _ = Z := (D.reconstruction _ Z).symm

end Paper28
