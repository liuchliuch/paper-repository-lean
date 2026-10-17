import Paper28.GroupHomSphereFolding
import Paper28.SphericalLiftedCurrentPresentation

/-! Canonical group-homomorphism sphere pushforward on actual finite
coordinate supported currents. For injective homomorphisms, the standard
coordinate-sign subdivision/integration compatibility is isolated as a
general PL/AK input, without a transfer or homology conclusion. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
variable {G K : Type} [Group G] [Group K] [DecidableEq G] [DecidableEq K] [Countable G] [Countable K]
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (Q : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere K) inferInstance)
  (F : CanonicalGlobalCurrentCalculusInput) (θ : G →* K)

def groupHomSphereCurrentPush :
    GlobalCurrentPushforwardInput inferInstance inferInstance J Q (groupHomSphereFold θ) :=
  F.map J Q _ ⟨1,groupHomSphereFold_lipschitz θ⟩

theorem groupHomSphereFold_support (E : Finset G) (u : RegularSphere G)
    (hu : u.val ∈ coordinateSupportSubspace E) :
    (groupHomSphereFold θ u).val ∈ coordinateSupportSubspace (E.image θ) := by
  intro b hb
  change ‖hilbertFiberRestriction θ b u.val‖ = 0
  apply norm_eq_zero.mpr
  ext i
  change u.val i.val = 0
  apply hu i.val
  intro hi
  exact hb (Finset.mem_image.mpr ⟨i.val,hi,i.property⟩)

def finiteCoordinateSphereFoldPush (k : ℕ) : finiteCoordinateSupportedCurrents J k →+ finiteCoordinateSupportedCurrents Q k where
  toFun C := ⟨(groupHomSphereCurrentPush J Q F θ).push k C.val,by
    obtain ⟨E,hE⟩ := C.property
    refine ⟨E.image θ,?_⟩
    intro x hx
    obtain ⟨u,hu,rfl⟩ := (groupHomSphereCurrentPush J Q F θ).support_subset k C.val hx
    exact groupHomSphereFold_support θ E u (hE hu)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' C D := Subtype.ext (map_add _ _ _)

/-- Standard finite geodesic subdivision under a coordinate monomorphism
after absolute value: cut each finite simplex by coordinate sign planes,
apply its isometric coordinate inclusion on each piece, and refine the
proper target charts. Only canonical integration compatibility is asserted.
This is the PL common-subdivision/AK change-of-variables corollary, not a
transfer, approximation, class recovery or mass estimate. -/
structure InjectiveGeodesicFoldingInput : Prop where
  simplex : ∀ {G K : Type} [Group G] [Group K] [DecidableEq G] [DecidableEq K] [Countable G] [Countable K]
    (MG : SphericalQuotientMetricInput G) (MK : SphericalQuotientMetricInput K)
    (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
    (Q : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere K) inferInstance)
    (LG : LiftedSphericalSimplexIntegrationInput (M := MG) J)
    (LK : LiftedSphericalSimplexIntegrationInput (M := MK) Q)
    (F : CanonicalGlobalCurrentCalculusInput) (θ : G →* K), Function.Injective θ →
    ∀ k (σ : LiftableSphericalSimplex MG k), ∃ z : FreeAbelianGroup (LiftableSphericalSimplex MK k),
      liftedSphericalChain LK k z = finiteCoordinateSphereFoldPush J Q F θ k (liftedSphericalGenerator LG k σ)

theorem injective_geodesic_folding_chain (PL : InjectiveGeodesicFoldingInput)
    {MG : SphericalQuotientMetricInput G} {MK : SphericalQuotientMetricInput K}
    (LG : LiftedSphericalSimplexIntegrationInput (M := MG) J)
    (LK : LiftedSphericalSimplexIntegrationInput (M := MK) Q)
    (hθ : Function.Injective θ) (k : ℕ) (z : FreeAbelianGroup (LiftableSphericalSimplex MG k)) :
    ∃ w : FreeAbelianGroup (LiftableSphericalSimplex MK k),
      liftedSphericalChain LK k w = finiteCoordinateSphereFoldPush J Q F θ k (liftedSphericalChain LG k z) := by
  refine FreeAbelianGroup.induction_on z ?_ ?_ ?_ ?_
  · exact ⟨0,by rw [map_zero,map_zero,map_zero]⟩
  · intro σ
    simpa only [liftedSphericalChain,FreeAbelianGroup.lift_apply_of] using PL.simplex MG MK J Q LG LK F θ hθ k σ
  · intro z hz
    obtain ⟨w,hw⟩ := hz
    exact ⟨-w,by simpa only [map_neg] using congrArg Neg.neg hw⟩
  · intro z z' hz hz'
    obtain ⟨w,hw⟩ := hz
    obtain ⟨w',hw'⟩ := hz'
    exact ⟨w+w',by simpa only [map_add] using congrArg₂ (fun a b => a+b) hw hw'⟩

end Paper28
