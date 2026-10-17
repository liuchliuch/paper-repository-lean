import Paper28.BassSerreFactorSphereRecovery
import Paper28.BassSerreRawTransfer
import Paper28.FiniteCoordinateHomFold
import Paper28.SongHomologyFrameworkInput
import Paper28.GlobalPushforwardSquares

/-! Native recovery of actual factor currents by the raw transfers.
At the central vertex the sum is the factor absolute-value pushforward;
all other summands vanish in positive degree by their proved constancy.
-/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B) (Grouping : HilbertGroupingInput)
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (JA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere A) inferInstance)
  (JB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere B) inferInstance)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (F : CanonicalGlobalCurrentCalculusInput)

include Grouping in
theorem bassSerreRawTransfer_factorA_A (Faithful : CurrentMassFaithfulnessInput IA)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents JA (k+1)) :
    bassSerreRawTransferA T MA J IA F Faithful k (finiteCoordinateSphereFoldPush JA J F A.subtype (k+1) C) =
      (groupHomCurrentPush F MA MA IA IA (MonoidHom.id A)).push (k+1)
        ((sphericalQuotientCurrentPush (I := IA) (J := JA) F).push (k+1) C.val) := by
  letI := MA.metric
  let N := finiteCoordinateSphereFoldPush JA J F A.subtype (k+1) C
  have hOff : ∀ v : G ⧸ A, v ≠ factorBaseCoset A → (bassSerreShadowPushA T MA J IA F v).push (k+1) N.val = 0 := by
    intro v hv
    obtain ⟨c,hc⟩ := bassSerreFactorA_shadowA_constant T Grouping v hv
    exact globalCurrentPush_composition_constant_zero F JA J IA Faithful
      (groupHomSphereFold A.subtype) (bassSerreQuotientShadowA T v)
      ⟨1,groupHomSphereFold_lipschitz A.subtype⟩ ⟨_,bassSerreQuotientShadowA_lipschitz T MA v⟩
      k C.val c (fun u _ => hc u)
  have hSingle : bassSerreRawTransferA T MA J IA F Faithful k N =
      (bassSerreShadowPushA T MA J IA F (factorBaseCoset A)).push (k+1) N.val :=
    Finsupp.sum_eq_single _ (fun v _ hv => hOff v hv) (fun _ => rfl)
  rw [hSingle]
  exact globalCurrentPush_square F JA J IA IA
    (groupHomSphereFold A.subtype) (bassSerreQuotientShadowA T (factorBaseCoset A))
    regularQuotientMap (groupHomQuotientFold (MonoidHom.id A))
    ⟨1,groupHomSphereFold_lipschitz A.subtype⟩ ⟨_,bassSerreQuotientShadowA_lipschitz T MA _⟩
    (sphericalQuotientMapLipschitz MA) ⟨1,groupHomQuotientFold_lipschitz MA MA _⟩
    (funext (bassSerreFactorA_shadow_center T Grouping)) (k+1) C.val

include Grouping in
theorem bassSerreRawTransfer_factorA_B (Faithful : CurrentMassFaithfulnessInput IB)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents JA (k+1)) :
    bassSerreRawTransferB T MB J IB F Faithful k (finiteCoordinateSphereFoldPush JA J F A.subtype (k+1) C) = 0 := by
  letI := MB.metric
  let N := finiteCoordinateSphereFoldPush JA J F A.subtype (k+1) C
  have hz : bassSerreShadowFamilyB T MB J IB F Faithful k N = 0 := by
    ext v
    obtain ⟨c,hc⟩ := bassSerreFactorA_shadowB_constant T Grouping v
    exact globalCurrentPush_composition_constant_zero F JA J IB Faithful
      (groupHomSphereFold A.subtype) (bassSerreQuotientShadowB T v)
      ⟨1,groupHomSphereFold_lipschitz A.subtype⟩ ⟨_,bassSerreQuotientShadowB_lipschitz T MB v⟩
      k C.val c (fun u _ => hc u)
  change (bassSerreShadowFamilyB T MB J IB F Faithful k N).sum (fun _ m => m) = 0
  rw [hz]
  rfl

include Grouping in
theorem bassSerreRawTransfer_factorB_A (Faithful : CurrentMassFaithfulnessInput IA)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents JB (k+1)) :
    bassSerreRawTransferA T MA J IA F Faithful k (finiteCoordinateSphereFoldPush JB J F B.subtype (k+1) C) = 0 := by
  letI := MA.metric
  let N := finiteCoordinateSphereFoldPush JB J F B.subtype (k+1) C
  have hz : bassSerreShadowFamilyA T MA J IA F Faithful k N = 0 := by
    ext v
    obtain ⟨c,hc⟩ := bassSerreFactorB_shadowA_constant T Grouping v
    exact globalCurrentPush_composition_constant_zero F JB J IA Faithful
      (groupHomSphereFold B.subtype) (bassSerreQuotientShadowA T v)
      ⟨1,groupHomSphereFold_lipschitz B.subtype⟩ ⟨_,bassSerreQuotientShadowA_lipschitz T MA v⟩
      k C.val c (fun u _ => hc u)
  change (bassSerreShadowFamilyA T MA J IA F Faithful k N).sum (fun _ m => m) = 0
  rw [hz]
  rfl

include Grouping in
theorem bassSerreRawTransfer_factorB_B (Faithful : CurrentMassFaithfulnessInput IB)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents JB (k+1)) :
    bassSerreRawTransferB T MB J IB F Faithful k (finiteCoordinateSphereFoldPush JB J F B.subtype (k+1) C) =
      (groupHomCurrentPush F MB MB IB IB (MonoidHom.id B)).push (k+1)
        ((sphericalQuotientCurrentPush (I := IB) (J := JB) F).push (k+1) C.val) := by
  letI := MB.metric
  let N := finiteCoordinateSphereFoldPush JB J F B.subtype (k+1) C
  have hOff : ∀ v : G ⧸ B, v ≠ factorBaseCoset B → (bassSerreShadowPushB T MB J IB F v).push (k+1) N.val = 0 := by
    intro v hv
    obtain ⟨c,hc⟩ := bassSerreFactorB_shadowB_constant T Grouping v hv
    exact globalCurrentPush_composition_constant_zero F JB J IB Faithful
      (groupHomSphereFold B.subtype) (bassSerreQuotientShadowB T v)
      ⟨1,groupHomSphereFold_lipschitz B.subtype⟩ ⟨_,bassSerreQuotientShadowB_lipschitz T MB v⟩
      k C.val c (fun u _ => hc u)
  have hSingle : bassSerreRawTransferB T MB J IB F Faithful k N =
      (bassSerreShadowPushB T MB J IB F (factorBaseCoset B)).push (k+1) N.val :=
    Finsupp.sum_eq_single _ (fun v _ hv => hOff v hv) (fun _ => rfl)
  rw [hSingle]
  exact globalCurrentPush_square F JB J IB IB
    (groupHomSphereFold B.subtype) (bassSerreQuotientShadowB T (factorBaseCoset B))
    regularQuotientMap (groupHomQuotientFold (MonoidHom.id B))
    ⟨1,groupHomSphereFold_lipschitz B.subtype⟩ ⟨_,bassSerreQuotientShadowB_lipschitz T MB _⟩
    (sphericalQuotientMapLipschitz MB) ⟨1,groupHomQuotientFold_lipschitz MB MB _⟩
    (funext (bassSerreFactorB_shadow_center T Grouping)) (k+1) C.val

end Paper28
