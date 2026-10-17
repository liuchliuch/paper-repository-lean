import Paper28.QuotientApproximationLemma
import Paper28.IntegralTransferProposition
import Paper28.SongHomologyFrameworkInput
import Paper28.FiniteCoordinateHomFold

/-! Named packaging of disclosed standard foundations. There is no own
approximation, filling, transfer, factor-recovery or additivity result in
either structure. The following wrapper invokes the proved Lemma 3.1.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28

structure PaperStandardInputs where
  currentCalculus : CanonicalGlobalCurrentCalculusInput
  fischer : FischerInput
  finiteRoundGeometry : FiniteRoundQuotientRealizationInput
  finiteRoundCurrents : FiniteRoundCurrentTransportInput
  fullNeighborhood : SphericalFullNeighborhoodInput
  geodesicRefinement : SphericalFiniteRefinementInput
  simplicialSingular : SimplicialSingularHomologyComparisonInput
  geodesicMass : GeodesicPolyhedralMassInput
  hilbertGrouping : HilbertGroupingInput
  injectiveFolding : InjectiveGeodesicFoldingInput
  bassSerre : BassSerreStructureInput
  groupHomology : IntegralGroupHomologyInput
  song : SongSphericalHomologyInput groupHomology currentCalculus

structure SphericalQuotientCurrentData (F : CanonicalGlobalCurrentCalculusInput)
    (G : Type) [Group G] [DecidableEq G] [Countable G] where
  M : SphericalQuotientMetricInput G
  algebra : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric
  sphereAlgebra : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance
  simplex : SphericalSimplexIntegrationInput M algebra.toCompactIntegralCurrentSupportInput
  lifted : LiftedSphericalSimplexIntegrationInput (M := M) sphereAlgebra
  gluing : SphericalCurrentGluingInput simplex lifted F
  localPush : CanonicalLocalPushforwardInput algebra
  homotopy : CompactCurrentHomotopyInput algebra
  massFaithful : CurrentMassFaithfulnessInput algebra
  finiteArea : FiniteCoordinateCurrentAreaInput sphereAlgebra

variable (Std : PaperStandardInputs) {G : Type} [Group G] [DecidableEq G] [Countable G]
  (D : SphericalQuotientCurrentData Std.currentCalculus G)

theorem quotientData_approximation (k : ℕ) :
    (∀ C : D.algebra.Current (k+1), D.algebra.boundary k C = 0 → ∀ ε : ℝ, 0 < ε →
      ∃ P : D.algebra.Current (k+1), ∃ W : D.algebra.Current (k+2),
        P ∈ sphericalPolyhedralCurrents D.simplex (k+1) ∧ D.algebra.boundary k P = 0 ∧
        C-P = D.algebra.boundary (k+1) W ∧ D.algebra.mass P ≤ D.algebra.mass C+ε) ∧
    (∀ Z : D.algebra.Current (k+1), Z ∈ sphericalPolyhedralCurrents D.simplex (k+1) →
      (∃ C : D.algebra.Current (k+2), D.algebra.boundary (k+1) C = Z) →
      ∃ Q : D.algebra.Current (k+2), Q ∈ sphericalPolyhedralCurrents D.simplex (k+2) ∧ D.algebra.boundary (k+1) Q = Z) :=
  lemma_3_1 D.M D.algebra D.simplex Std.finiteRoundGeometry Std.finiteRoundCurrents
    Std.fullNeighborhood Std.geodesicRefinement Std.simplicialSingular D.localPush D.homotopy k

def quotientDataComparison := Std.song.comparison D.M D.algebra

end Paper28
