import Paper28.BassSerreTransferBoundary
import Paper28.BassSerreRawTransferMass
import Paper28.GeodesicPolyhedralMassInput

/-! Original joint mass inequality (11). The actual single-simplex
bound follows from the native finite-hull Jacobian/area argument. The
finite disjoint integer presentation is standard PL/AK compatibility;
integer linear assembly and cancellation in both images are proved here.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  {J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance}
  (L : LiftedSphericalSimplexIntegrationInput (M := M) J) (F : CanonicalGlobalCurrentCalculusInput)
  {A B : Subgroup G} (T : BassSerreObject A B)
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (Gluing : SphericalCurrentGluingInput S L F)
  (FaithfulA : CurrentMassFaithfulnessInput IA) (FaithfulB : CurrentMassFaithfulnessInput IB)
  (Area : FiniteCoordinateCurrentAreaInput J)

include Area in
theorem bassSerreTransfer_simplex_joint_mass (Fischer : FischerInput) (k : ℕ) (hk : 4 ≤ k+1)
    (σ : LiftableSphericalSimplex M (k+1)) :
    IA.mass (bassSerreTransferA L F T MA IA S Gluing FaithfulA k (projectedSphericalGenerator S (k+1) σ))+
      IB.mass (bassSerreTransferB L F T MB IB S Gluing FaithfulB k (projectedSphericalGenerator S (k+1) σ)) ≤
        J.mass (L.integration (k+1) σ) := by
  unfold projectedSphericalGenerator
  rw [bassSerreTransferA_simplex,bassSerreTransferB_simplex]
  exact bassSerreRawTransfer_joint_mass T MA MB J IA IB F FaithfulA FaithfulB Area Fischer k hk
    (liftedSphericalGenerator L (k+1) σ)

include Area in
theorem bassSerreTransfer_joint_mass (Mass : GeodesicPolyhedralMassInput) (Fischer : FischerInput)
    (k : ℕ) (hk : 4 ≤ k+1) (P : sphericalPolyhedralCurrents S (k+1)) :
    IA.mass (bassSerreTransferA L F T MA IA S Gluing FaithfulA k P)+
      IB.mass (bassSerreTransferB L F T MB IB S Gluing FaithfulB k P) ≤ I.mass P.val := by
  obtain ⟨D⟩ := Mass.presentation S L (k+1) P
  let TA := bassSerreTransferA L F T MA IA S Gluing FaithfulA k
  let TB := bassSerreTransferB L F T MB IB S Gluing FaithfulB k
  let gen := fun i : Fin D.count => projectedSphericalGenerator S (k+1) (D.simplex i)
  have hTA : TA P = ∑ i, D.coefficient i • TA (gen i) := by
    simpa only [map_sum,map_zsmul] using congrArg TA D.current_formula
  have hTB : TB P = ∑ i, D.coefficient i • TB (gen i) := by
    simpa only [map_sum,map_zsmul] using congrArg TB D.current_formula
  have hPiece : ∀ i : Fin D.count, IA.mass (TA (gen i))+IB.mass (TB (gen i)) ≤ J.mass (L.integration (k+1) (D.simplex i)) :=
    fun i => bassSerreTransfer_simplex_joint_mass L F T MA MB IA IB S Gluing FaithfulA FaithfulB Area Fischer k hk (D.simplex i)
  change IA.mass (TA P)+IB.mass (TB P) ≤ _
  rw [hTA,hTB]
  calc
    _ ≤ (∑ i, IA.mass (D.coefficient i • TA (gen i)))+(∑ i, IB.mass (D.coefficient i • TB (gen i))) :=
      add_le_add (current_mass_finset_sum_le IA _ _) (current_mass_finset_sum_le IB _ _)
    _ ≤ (∑ i, |(D.coefficient i : ℝ)| * IA.mass (TA (gen i)))+
        (∑ i, |(D.coefficient i : ℝ)| * IB.mass (TB (gen i))) :=
      add_le_add (Finset.sum_le_sum (fun i _ => current_mass_zsmul_le IA _ _))
        (Finset.sum_le_sum (fun i _ => current_mass_zsmul_le IB _ _))
    _ = ∑ i, |(D.coefficient i : ℝ)| * (IA.mass (TA (gen i))+IB.mass (TB (gen i))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ ∑ i, |(D.coefficient i : ℝ)| * J.mass (L.integration (k+1) (D.simplex i)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hPiece i) (abs_nonneg _))
    _ = I.mass P.val := D.mass_formula.symm

end Paper28
