import Paper28.RelativeCurrentDeformation
import Paper28.CanonicalLocalPushforwardInput

/-! The first stage of original Lemma 3.1, on actual quotient currents.
The actual relative deformation is constructed by Lemma 5.1; generic AK
calculus then gives a homologous current of arbitrarily close mass in an
actual finite coordinate carrier, and a carrier filling fixing the exact
prescribed polyhedral boundary. Carrier triangulation is a separate step. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  (M : SphericalQuotientMetricInput G)
  (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric)
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (Push : CanonicalLocalPushforwardInput I)

include S Push in
theorem sharp_finite_carrier_current_stage (H : CompactCurrentHomotopyInput I) {k : ℕ}
    (C : I.Current (k+1)) (hC : I.boundary k C = 0) (ε : ℝ) (hε : 0 < ε) :
    ∃ families : Finset (Finset G), (∀ E ∈ families, (1 : G) ∈ E) ∧
      ∃ E : I.Current (k+1), ∃ W : I.Current (k+2),
        I.boundary k E = 0 ∧ C-E = I.boundary (k+1) W ∧
        I.support E ⊆ quotientFiniteCarrier families ∧ I.mass E ≤ I.mass C+ε := by
  letI := M.metric
  obtain ⟨η,hη,hηMass⟩ := exists_positive_eta_mass_control (k+1) (I.mass C) ε hε
  obtain ⟨F⟩ := lemma_5_1 M I.toCompactIntegralCurrentSupportInput S (I.support C) (I.support_compact C)
    0 (0 : I.Current 0) (AddSubgroup.zero_mem _) (by rw [I.support_zero]; exact empty_subset _) η hη
  obtain ⟨P,Local⟩ := Push.pushforward F.neighborhood (relativeDeformationExtension F) F.neighborhood_open
    (relativeDeformationExtension_lipschitz F)
  obtain ⟨E,W,hCycle,hHom,hSupport,hMass⟩ := relative_deformation_current_cycle F I P Local H C (Subset.refl _) hC
  exact ⟨F.families,F.coordinates_nonempty,E,W,hCycle,hHom,hSupport,hMass.trans hηMass⟩

include Push in
theorem relative_finite_carrier_filling_stage {k : ℕ}
    (Z : I.Current (k+1)) (hZ : Z ∈ sphericalPolyhedralCurrents S (k+1))
    (C : I.Current (k+2)) (hC : I.boundary (k+1) C = Z) :
    ∃ families : Finset (Finset G), (∀ E ∈ families, (1 : G) ∈ E) ∧
      ∃ E : I.Current (k+2), I.boundary (k+1) E = Z ∧
        I.support E ⊆ quotientFiniteCarrier families := by
  letI := M.metric
  have hZK : I.support Z ⊆ I.support C := by
    rw [← hC]
    exact I.support_boundary_subset (k+1) C
  obtain ⟨F⟩ := lemma_5_1 M I.toCompactIntegralCurrentSupportInput S (I.support C) (I.support_compact C)
    (k+1) Z hZ hZK 1 (by norm_num)
  obtain ⟨P,Local⟩ := Push.pushforward F.neighborhood (relativeDeformationExtension F) F.neighborhood_open
    (relativeDeformationExtension_lipschitz F)
  refine ⟨F.families,F.coordinates_nonempty,P.push (k+2) ⟨C,F.contains⟩,?_,
    relative_deformation_current_support F I P C (Subset.refl _)⟩
  exact (relative_deformation_preserves_boundary F I P Local C (Subset.refl _)
    (by rw [hC])).trans hC

end Paper28
