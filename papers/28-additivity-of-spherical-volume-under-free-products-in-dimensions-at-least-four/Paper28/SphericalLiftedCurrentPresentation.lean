import Paper28.FiniteCoordinateCurrentTranslation
import Paper28.SphericalPolyhedralCurrents
import Paper28.LiftableSimplexOverlaps
import Paper28.GlobalAngularChordBound
import Mathlib.GroupTheory.FreeAbelianGroup

/-! Canonical lifted simplex integration objects and native finite integer
presentations of the actual source polyhedral current subgroup. General
common-refinement gluing is specified separately, with no shadow or
transfer in its signature. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G : Type} [Group G] [DecidableEq G] [Countable G]
  {M : SphericalQuotientMetricInput G}
  {I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) M.metric}
  (S : SphericalSimplexIntegrationInput M I.toCompactIntegralCurrentSupportInput)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)

/-- The standard actual oriented integration current on each lifted
normalized spherical simplex; this is an object API, without estimates. -/
structure LiftedSphericalSimplexIntegrationInput where
  integration : ∀ k, LiftableSphericalSimplex M k → J.Current k
  support_subset : ∀ k (σ : LiftableSphericalSimplex M k), J.support (integration k σ) ⊆ σ.liftedPatch

variable {J} (L : LiftedSphericalSimplexIntegrationInput (M := M) J)

def liftedSphericalGenerator (k : ℕ) (σ : LiftableSphericalSimplex M k) : finiteCoordinateSupportedCurrents J k :=
  ⟨L.integration k σ,⟨σ.coordinates,fun u hu => σ.liftedPatch_supported u (L.support_subset k σ hu)⟩⟩

def liftedSphericalChain (k : ℕ) :
    FreeAbelianGroup (LiftableSphericalSimplex M k) →+ finiteCoordinateSupportedCurrents J k :=
  FreeAbelianGroup.lift (liftedSphericalGenerator L k)

def projectedSphericalChain (k : ℕ) :
    FreeAbelianGroup (LiftableSphericalSimplex M k) →+ sphericalPolyhedralCurrents S k :=
  FreeAbelianGroup.lift (fun σ => ⟨S.integration k σ,AddSubgroup.subset_closure ⟨σ,rfl⟩⟩)

theorem projectedSphericalChain_surjective (k : ℕ) : Function.Surjective (projectedSphericalChain S k) := by
  rintro ⟨C,hC⟩
  have h : ∃ z : FreeAbelianGroup (LiftableSphericalSimplex M k),
      (projectedSphericalChain S k z).val = C := by
    induction hC using AddSubgroup.closure_induction with
    | mem C hC =>
      obtain ⟨σ,rfl⟩ := hC
      exact ⟨FreeAbelianGroup.of σ,by rw [projectedSphericalChain,FreeAbelianGroup.lift_apply_of]⟩
    | zero => exact ⟨0,by rw [map_zero]; rfl⟩
    | add C D _ _ hC hD =>
      obtain ⟨z,hz⟩ := hC
      obtain ⟨w,hw⟩ := hD
      exact ⟨z+w,by rw [map_add]; change (projectedSphericalChain S k z).val+(projectedSphericalChain S k w).val = _; rw [hz,hw]⟩
    | neg C _ hC =>
      obtain ⟨z,hz⟩ := hC
      exact ⟨-z,by rw [map_neg]; change -(projectedSphericalChain S k z).val = _; rw [hz]⟩
  obtain ⟨z,hz⟩ := h
  exact ⟨z,Subtype.ext hz⟩

def sphericalLiftRelations (F : CanonicalGlobalCurrentCalculusInput) (k : ℕ) :
    AddSubgroup (FreeAbelianGroup (LiftableSphericalSimplex M k)) :=
  AddSubgroup.closure ({z | liftedSphericalChain L k z = 0} ∪
    {w | ∃ (γ : G) (z z' : FreeAbelianGroup (LiftableSphericalSimplex M k)),
      w = z-z' ∧ liftedSphericalChain L k z' = finiteCoordinateCurrentAction J F γ k (liftedSphericalChain L k z)})

def sphericalQuotientMapLipschitz (M : SphericalQuotientMetricInput G) :
    letI := M.metric
    ∃ K : NNReal, LipschitzWith K (regularQuotientMap : RegularSphere G → RegularOrbitQuotient G) := by
  letI := M.metric
  refine ⟨⟨Real.pi/2,by positivity⟩,LipschitzWith.of_dist_le_mul (fun u v => ?_)⟩
  have h := spherical_quotient_dist_le_angle M u v 1
  rw [leftRegular_one] at h
  exact h.trans (angular_le_pi_half_chord u.val v.val u.property v.property)

def sphericalQuotientCurrentPush (F : CanonicalGlobalCurrentCalculusInput) :
    GlobalCurrentPushforwardInput inferInstance M.metric J I regularQuotientMap := by
  letI := M.metric
  exact F.map J I regularQuotientMap (sphericalQuotientMapLipschitz M)

/-- Standard geodesic common-subdivision/coefficient-separation gluing
for proper charts of a discrete isometric quotient. This is the generic
polyhedral current presentation corollary of PL common refinement and
canonical integration locality, not a transfer-independence premise.
The relations are actual lifted-current cancellation and group translation.
The last field is ordinary simplex Stokes with common refinement of faces.
No averaging, transfer, mass bound, cycle or filling occurs here. -/
structure SphericalCurrentGluingInput (F : CanonicalGlobalCurrentCalculusInput) : Prop where
  projected_compatibility : ∀ k z,
    (sphericalQuotientCurrentPush (I := I) (J := J) F).push k (liftedSphericalChain L k z).val =
      (projectedSphericalChain S k z).val
  kernel_gluing : ∀ k, (projectedSphericalChain S k).ker ≤ sphericalLiftRelations L F k
  simplex_stokes_refinement : ∀ k (σ : LiftableSphericalSimplex M (k+1)),
    ∃ z : FreeAbelianGroup (LiftableSphericalSimplex M k),
      liftedSphericalChain L k z = finiteCoordinateBoundary J k (liftedSphericalGenerator L (k+1) σ)

end Paper28
