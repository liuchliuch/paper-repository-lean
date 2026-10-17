import Paper28.FiniteRoundCurrentTransportInput
import Paper28.FiniteCarrierCurrentStage

/-! Original Lemma 3.1. The actual relative near-isometric deformation
is combined with the proved sharp finite spherical-polyhedron theorem.
General finite spherical realization and canonical AK transport remain
precisely disclosed external parameters; neither assumes approximation
or a prescribed filling. Positive degree is written k+1. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set Filter
open scoped Topology
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  (M : SphericalQuotientMetricInput G)
  (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric)
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (Geometry : FiniteRoundQuotientRealizationInput) (AK : FiniteRoundCurrentTransportInput)
  (PL : SphericalFullNeighborhoodInput) (Ref : SphericalFiniteRefinementInput)
  (SS : SimplicialSingularHomologyComparisonInput)

include Geometry AK PL Ref SS in
theorem finite_carrier_current_approximation {k : ℕ}
    (families : Finset (Finset G)) (C : I.Current (k+1)) (hC : I.boundary k C = 0)
    (hSupport : I.support C ⊆ quotientFiniteCarrier families) (ε : ℝ) (hε : 0 < ε) :
    ∃ P : I.Current (k+1), ∃ D : I.Current (k+2),
      P ∈ sphericalPolyhedralCurrents S (k+1) ∧ I.boundary k P = 0 ∧
      C-P = I.boundary (k+1) D ∧ I.mass P ≤ I.mass C+ε := by
  obtain ⟨Cover⟩ := finite_carrier_spherical_presentation (M := M) families
  obtain ⟨R⟩ := Geometry.realization M _ Cover
  obtain ⟨T⟩ := AK.transport R I S
  let C₀ := (T.identification (k+1)).symm ⟨C,hSupport⟩
  have hC₀ : T.algebra.boundary k C₀ = 0 := by
    rw [roundModelPull_boundary]
    have hz : supportedBoundary I (quotientFiniteCarrier families) k ⟨C,hSupport⟩ = 0 := Subtype.ext hC
    rw [hz,map_zero]
  obtain ⟨Pi,Di,hPoly,hCycle,hHom,_,hMass⟩ :=
    (lemma_5_2 R.polyhedron T.algebra T.componentAlgebra T.decomposition T.integration
      T.foundations PL Ref T.comparison SS k).1 C₀ hC₀
  have hMassC : T.algebra.mass C₀ = I.mass C := by
    have he := T.mass_compatibility (k+1) C₀
    dsimp [C₀] at he
    rw [AddEquiv.apply_symm_apply] at he
    exact he.symm
  have hevent : ∀ᶠ i in atTop, T.algebra.mass (Pi i) < I.mass C+ε :=
    (tendsto_order.mp hMass).2 _ (by rw [hMassC]; linarith)
  obtain ⟨i,hi⟩ := hevent.exists
  refine ⟨roundModelPush T (k+1) (Pi i),roundModelPush T (k+2) (Di i),
    (roundModelPush_polyhedral T _ _).mp (hPoly i),?_,?_,?_⟩
  · rw [roundModelPush_boundary,hCycle i,map_zero]
  · have he := congrArg (roundModelPush T (k+1)) (hHom i)
    rw [map_sub,← roundModelPush_boundary] at he
    have hPushC : roundModelPush T (k+1) C₀ = C :=
      congrArg Subtype.val ((T.identification (k+1)).apply_symm_apply ⟨C,hSupport⟩)
    rwa [hPushC] at he
  · rw [roundModelPush_mass]
    exact hi.le

include Geometry AK PL Ref SS in
theorem finite_carrier_prescribed_filling {k : ℕ}
    (families : Finset (Finset G)) (Z : I.Current (k+1))
    (hZ : Z ∈ sphericalPolyhedralCurrents S (k+1))
    (C : I.Current (k+2)) (hC : I.boundary (k+1) C = Z)
    (hSupport : I.support C ⊆ quotientFiniteCarrier families) :
    ∃ Q : I.Current (k+2), Q ∈ sphericalPolyhedralCurrents S (k+2) ∧ I.boundary (k+1) Q = Z := by
  obtain ⟨Cover⟩ := finite_carrier_spherical_presentation (M := M) families
  obtain ⟨R⟩ := Geometry.realization M _ Cover
  obtain ⟨T⟩ := AK.transport R I S
  have hZS : I.support Z ⊆ quotientFiniteCarrier families :=
    hC ▸ (I.support_boundary_subset (k+1) C).trans hSupport
  let Z₀ := (T.identification (k+1)).symm ⟨Z,hZS⟩
  let C₀ := (T.identification (k+2)).symm ⟨C,hSupport⟩
  have hPushZ : roundModelPush T (k+1) Z₀ = Z :=
    congrArg Subtype.val ((T.identification (k+1)).apply_symm_apply ⟨Z,hZS⟩)
  have hPoly : Z₀ ∈ finiteSphericalPolyhedralCurrents R.polyhedron T.decomposition T.integration (k+1) := by
    apply (roundModelPush_polyhedral T _ _).mpr
    rwa [hPushZ]
  have hBoundary : T.algebra.boundary (k+1) C₀ = Z₀ := by
    rw [roundModelPull_boundary]
    apply congrArg (T.identification (k+1)).symm
    exact Subtype.ext hC
  obtain ⟨Q,hQ,hb⟩ :=
    (lemma_5_2 R.polyhedron T.algebra T.componentAlgebra T.decomposition T.integration
      T.foundations PL Ref T.comparison SS k).2 Z₀ hPoly ⟨C₀,hBoundary⟩
  exact ⟨roundModelPush T (k+2) Q,(roundModelPush_polyhedral T _ _).mp hQ,
    (roundModelPush_boundary T (k+1) Q).trans ((congrArg (roundModelPush T (k+1)) hb).trans hPushZ)⟩

include Geometry AK PL Ref SS in
theorem lemma_3_1 (Push : CanonicalLocalPushforwardInput I) (H : CompactCurrentHomotopyInput I) (k : ℕ) :
    (∀ C : I.Current (k+1), I.boundary k C = 0 → ∀ ε : ℝ, 0 < ε →
      ∃ P : I.Current (k+1), ∃ D : I.Current (k+2),
        P ∈ sphericalPolyhedralCurrents S (k+1) ∧ I.boundary k P = 0 ∧
        C-P = I.boundary (k+1) D ∧ I.mass P ≤ I.mass C+ε) ∧
    (∀ Z : I.Current (k+1), Z ∈ sphericalPolyhedralCurrents S (k+1) →
      (∃ C : I.Current (k+2), I.boundary (k+1) C = Z) →
      ∃ Q : I.Current (k+2), Q ∈ sphericalPolyhedralCurrents S (k+2) ∧ I.boundary (k+1) Q = Z) := by
  constructor
  · intro C hC ε hε
    obtain ⟨families,_,E,W,hE,hCW,hES,hEM⟩ := sharp_finite_carrier_current_stage M I S Push H C hC (ε/2) (by linarith)
    obtain ⟨P,D,hP,hPC,hEP,hPM⟩ := finite_carrier_current_approximation M I S Geometry AK PL Ref SS
      families E hE hES (ε/2) (by linarith)
    refine ⟨P,W+D,hP,hPC,?_,by linarith⟩
    rw [map_add,← hCW,← hEP]
    abel
  · rintro Z hZ ⟨C,hC⟩
    obtain ⟨families,_,E,hE,hES⟩ := relative_finite_carrier_filling_stage M I S Push Z hZ C hC
    exact finite_carrier_prescribed_filling M I S Geometry AK PL Ref SS families Z hZ E hE hES

end Paper28
