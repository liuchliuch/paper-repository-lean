import Paper28.BassSerreRawTransferEquivariance
import Paper28.SphericalLiftedCurrentPresentation
import Paper28.SurjectiveAdditiveDescent

/-! Native descent of the concrete integral shadow sums through the
actual source polyhedral-current presentations. General geodesic current
gluing supplies only its current-cancellation/translation relations. The
actual shadow sums kill those relations by additivity and equation (8),
so lift and presentation independence are proved here. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  {J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance}
  (L : LiftedSphericalSimplexIntegrationInput (M := M) J) (F : CanonicalGlobalCurrentCalculusInput)

theorem sphericalLiftRelations_killed {N : Type*} [AddCommGroup N] (k : ℕ)
    (g : finiteCoordinateSupportedCurrents J k →+ N)
    (hInv : ∀ γ C, g (finiteCoordinateCurrentAction J F γ k C) = g C) :
    sphericalLiftRelations L F k ≤ (g.comp (liftedSphericalChain L k)).ker := by
  apply (AddSubgroup.closure_le _).mpr
  intro w hw
  rcases hw with hw | hw
  · change g (liftedSphericalChain L k w) = 0
    rw [hw,map_zero]
  · obtain ⟨γ,z,z',rfl,he⟩ := hw
    change g (liftedSphericalChain L k (z-z')) = 0
    rw [map_sub,map_sub,he,hInv,sub_self]

variable {A B : Subgroup G} (T : BassSerreObject A B)
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (Gluing : SphericalCurrentGluingInput S L F)

include Gluing in
theorem bassSerreTransferA_kernel (Faithful : CurrentMassFaithfulnessInput IA) (k : ℕ) :
    (projectedSphericalChain S (k+1)).ker ≤
      ((bassSerreRawTransferA T MA J IA F Faithful k).comp (liftedSphericalChain L (k+1))).ker :=
  (Gluing.kernel_gluing (k+1)).trans (sphericalLiftRelations_killed L F (k+1) _
    (bassSerreRawTransferA_translate T MA J IA F Faithful (k := k)))

include Gluing in
theorem bassSerreTransferB_kernel (Faithful : CurrentMassFaithfulnessInput IB) (k : ℕ) :
    (projectedSphericalChain S (k+1)).ker ≤
      ((bassSerreRawTransferB T MB J IB F Faithful k).comp (liftedSphericalChain L (k+1))).ker :=
  (Gluing.kernel_gluing (k+1)).trans (sphericalLiftRelations_killed L F (k+1) _
    (bassSerreRawTransferB_translate T MB J IB F Faithful (k := k)))

def bassSerreTransferA (Faithful : CurrentMassFaithfulnessInput IA) (k : ℕ) :
    sphericalPolyhedralCurrents S (k+1) →+ IA.Current (k+1) :=
  additiveSurjectiveDescent (projectedSphericalChain S (k+1))
    ((bassSerreRawTransferA T MA J IA F Faithful k).comp (liftedSphericalChain L (k+1)))
    (bassSerreTransferA_kernel L F T MA IA S Gluing Faithful k) (projectedSphericalChain_surjective S (k+1))

def bassSerreTransferB (Faithful : CurrentMassFaithfulnessInput IB) (k : ℕ) :
    sphericalPolyhedralCurrents S (k+1) →+ IB.Current (k+1) :=
  additiveSurjectiveDescent (projectedSphericalChain S (k+1))
    ((bassSerreRawTransferB T MB J IB F Faithful k).comp (liftedSphericalChain L (k+1)))
    (bassSerreTransferB_kernel L F T MB IB S Gluing Faithful k) (projectedSphericalChain_surjective S (k+1))

theorem bassSerreTransferA_presentation (Faithful : CurrentMassFaithfulnessInput IA) (k : ℕ)
    (z : FreeAbelianGroup (LiftableSphericalSimplex M (k+1))) :
    bassSerreTransferA L F T MA IA S Gluing Faithful k (projectedSphericalChain S (k+1) z) =
      bassSerreRawTransferA T MA J IA F Faithful k (liftedSphericalChain L (k+1) z) :=
  additiveSurjectiveDescent_apply _ _ _ _ z

theorem bassSerreTransferB_presentation (Faithful : CurrentMassFaithfulnessInput IB) (k : ℕ)
    (z : FreeAbelianGroup (LiftableSphericalSimplex M (k+1))) :
    bassSerreTransferB L F T MB IB S Gluing Faithful k (projectedSphericalChain S (k+1) z) =
      bassSerreRawTransferB T MB J IB F Faithful k (liftedSphericalChain L (k+1) z) :=
  additiveSurjectiveDescent_apply _ _ _ _ z

end Paper28
