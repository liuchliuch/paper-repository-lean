import Paper28.BassSerreTransferDescent
import Paper28.SphericalPolyhedralBoundary
import Paper28.BassSerreRawTransferBoundary

/-! Equation (10) after the actual transfer has descended to quotient
polyhedral currents. The comparison of arbitrary presentations and the
ordinary simplex Stokes refinements are assembled natively. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
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

theorem bassSerreTransferA_boundary (Faithful : CurrentMassFaithfulnessInput IA)
    (k : ℕ) (P : sphericalPolyhedralCurrents S (k+2)) :
    IA.boundary (k+1) (bassSerreTransferA L F T MA IA S Gluing Faithful (k+1) P) =
      bassSerreTransferA L F T MA IA S Gluing Faithful k (sphericalPolyhedralBoundary S L F Gluing (k+1) P) := by
  obtain ⟨z,hz⟩ := projectedSphericalChain_surjective S (k+2) P
  obtain ⟨w,hw⟩ := sphericalChain_boundary_refinement S L F Gluing (k+1) z
  have hPw : projectedSphericalChain S (k+1) w = sphericalPolyhedralBoundary S L F Gluing (k+1) P := by
    apply Subtype.ext
    have he := projectedSphericalChain_boundary S L F Gluing (k+1) z w hw
    rwa [hz] at he
  calc
    _ = IA.boundary (k+1) (bassSerreRawTransferA T MA J IA F Faithful (k+1) (liftedSphericalChain L (k+2) z)) := by
      rw [← hz,bassSerreTransferA_presentation]
    _ = bassSerreRawTransferA T MA J IA F Faithful k (finiteCoordinateBoundary J (k+1) (liftedSphericalChain L (k+2) z)) :=
      bassSerreRawTransferA_boundary T MA J IA F Faithful k _
    _ = bassSerreRawTransferA T MA J IA F Faithful k (liftedSphericalChain L (k+1) w) := congrArg _ hw.symm
    _ = bassSerreTransferA L F T MA IA S Gluing Faithful k (projectedSphericalChain S (k+1) w) :=
      (bassSerreTransferA_presentation L F T MA IA S Gluing Faithful k w).symm
    _ = _ := congrArg _ hPw

theorem bassSerreTransferB_boundary (Faithful : CurrentMassFaithfulnessInput IB)
    (k : ℕ) (P : sphericalPolyhedralCurrents S (k+2)) :
    IB.boundary (k+1) (bassSerreTransferB L F T MB IB S Gluing Faithful (k+1) P) =
      bassSerreTransferB L F T MB IB S Gluing Faithful k (sphericalPolyhedralBoundary S L F Gluing (k+1) P) := by
  obtain ⟨z,hz⟩ := projectedSphericalChain_surjective S (k+2) P
  obtain ⟨w,hw⟩ := sphericalChain_boundary_refinement S L F Gluing (k+1) z
  have hPw : projectedSphericalChain S (k+1) w = sphericalPolyhedralBoundary S L F Gluing (k+1) P := by
    apply Subtype.ext
    have he := projectedSphericalChain_boundary S L F Gluing (k+1) z w hw
    rwa [hz] at he
  calc
    _ = IB.boundary (k+1) (bassSerreRawTransferB T MB J IB F Faithful (k+1) (liftedSphericalChain L (k+2) z)) := by
      rw [← hz,bassSerreTransferB_presentation]
    _ = bassSerreRawTransferB T MB J IB F Faithful k (finiteCoordinateBoundary J (k+1) (liftedSphericalChain L (k+2) z)) :=
      bassSerreRawTransferB_boundary T MB J IB F Faithful k _
    _ = bassSerreRawTransferB T MB J IB F Faithful k (liftedSphericalChain L (k+1) w) := congrArg _ hw.symm
    _ = bassSerreTransferB L F T MB IB S Gluing Faithful k (projectedSphericalChain S (k+1) w) :=
      (bassSerreTransferB_presentation L F T MB IB S Gluing Faithful k w).symm
    _ = _ := congrArg _ hPw

theorem bassSerreTransferA_simplex (Faithful : CurrentMassFaithfulnessInput IA) (k : ℕ)
    (σ : LiftableSphericalSimplex M (k+1)) :
    bassSerreTransferA L F T MA IA S Gluing Faithful k
      ⟨S.integration (k+1) σ,AddSubgroup.subset_closure ⟨σ,rfl⟩⟩ =
      (bassSerreShadowFamilyA T MA J IA F Faithful k (liftedSphericalGenerator L (k+1) σ)).sum (fun _ C => C) := by
  simpa only [projectedSphericalChain,liftedSphericalChain,FreeAbelianGroup.lift_apply_of] using
    bassSerreTransferA_presentation L F T MA IA S Gluing Faithful k (FreeAbelianGroup.of σ)

theorem bassSerreTransferB_simplex (Faithful : CurrentMassFaithfulnessInput IB) (k : ℕ)
    (σ : LiftableSphericalSimplex M (k+1)) :
    bassSerreTransferB L F T MB IB S Gluing Faithful k
      ⟨S.integration (k+1) σ,AddSubgroup.subset_closure ⟨σ,rfl⟩⟩ =
      (bassSerreShadowFamilyB T MB J IB F Faithful k (liftedSphericalGenerator L (k+1) σ)).sum (fun _ C => C) := by
  simpa only [projectedSphericalChain,liftedSphericalChain,FreeAbelianGroup.lift_apply_of] using
    bassSerreTransferB_presentation L F T MB IB S Gluing Faithful k (FreeAbelianGroup.of σ)

end Paper28
