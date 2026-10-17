import Paper28.FiniteCoordinateHomFold
import Paper28.SongHomologyFrameworkInput
import Paper28.GlobalPushforwardSquares

/-! Native quotient-level polyhedral preservation for an injective group
map, from the disclosed ordinary sign-cut/integration refinement. The
actual commuting quotient square is checked, with no transfer conclusion.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G K : Type} [Group G] [Group K] [DecidableEq G] [DecidableEq K] [Countable G] [Countable K]
  (MG : SphericalQuotientMetricInput G) (MK : SphericalQuotientMetricInput K)
  (I : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient G) MG.metric)
  (Q : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient K) MK.metric)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (R : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere K) inferInstance)
  (S : SphericalSimplexIntegrationInput MG I.toCompactIntegralCurrentSupportInput)
  (T : SphericalSimplexIntegrationInput MK Q.toCompactIntegralCurrentSupportInput)
  (LG : LiftedSphericalSimplexIntegrationInput (M := MG) J)
  (LK : LiftedSphericalSimplexIntegrationInput (M := MK) R)
  (F : CanonicalGlobalCurrentCalculusInput)
  (GG : SphericalCurrentGluingInput S LG F) (GK : SphericalCurrentGluingInput T LK F)
  (PL : InjectiveGeodesicFoldingInput) (θ : G →* K) (hθ : Function.Injective θ)

include GG GK in
theorem homFold_projected_lift (k : ℕ)
    (z : FreeAbelianGroup (LiftableSphericalSimplex MG k))
    (w : FreeAbelianGroup (LiftableSphericalSimplex MK k))
    (hw : liftedSphericalChain LK k w = finiteCoordinateSphereFoldPush J R F θ k (liftedSphericalChain LG k z)) :
    (projectedSphericalChain T k w).val =
      (groupHomCurrentPush F MG MK I Q θ).push k (projectedSphericalChain S k z).val := by
  letI := MG.metric
  letI := MK.metric
  have he := congrArg (fun C : finiteCoordinateSupportedCurrents R k =>
    (sphericalQuotientCurrentPush (I := Q) (J := R) F).push k C.val) hw
  dsimp only at he
  rw [GK.projected_compatibility] at he
  have hsquare := globalCurrentPush_square F J R Q I
    (groupHomSphereFold θ) regularQuotientMap regularQuotientMap (groupHomQuotientFold θ)
    ⟨1,groupHomSphereFold_lipschitz θ⟩ (sphericalQuotientMapLipschitz MK)
    (sphericalQuotientMapLipschitz MG) ⟨1,groupHomQuotientFold_lipschitz MG MK θ⟩ rfl k (liftedSphericalChain LG k z).val
  change _ = (sphericalQuotientCurrentPush (I := Q) (J := R) F).push k
    ((groupHomSphereCurrentPush J R F θ).push k (liftedSphericalChain LG k z).val) at he
  have hh : (projectedSphericalChain T k w).val = (groupHomCurrentPush F MG MK I Q θ).push k
      ((sphericalQuotientCurrentPush (I := I) (J := J) F).push k (liftedSphericalChain LG k z).val) := he.trans hsquare
  rw [GG.projected_compatibility] at hh
  exact hh

include GG GK PL hθ in
theorem homFold_polyhedral_mem (k : ℕ) (P : sphericalPolyhedralCurrents S k) :
    (groupHomCurrentPush F MG MK I Q θ).push k P.val ∈ sphericalPolyhedralCurrents T k := by
  obtain ⟨z,hz⟩ := projectedSphericalChain_surjective S k P
  obtain ⟨w,hw⟩ := injective_geodesic_folding_chain J R F θ PL LG LK hθ k z
  have he := homFold_projected_lift MG MK I Q J R S T LG LK F GG GK θ k z w hw
  rw [hz] at he
  exact he ▸ (projectedSphericalChain T k w).property

def homFoldPolyhedralPush (k : ℕ) : sphericalPolyhedralCurrents S k →+ sphericalPolyhedralCurrents T k where
  toFun P := ⟨(groupHomCurrentPush F MG MK I Q θ).push k P.val,
    homFold_polyhedral_mem MG MK I Q J R S T LG LK F GG GK PL θ hθ k P⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' C D := Subtype.ext (map_add _ _ _)

end Paper28
