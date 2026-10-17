import Paper28.BassSerreRawTransfer
import Paper28.FiniteCoordinateCurrentTranslation

/-! Lift changes permute the actual finite vertex-indexed current family.
The proof uses native shadow equivariance and generic AK functoriality.
The resulting sum is invariant, retaining all integer multiplicities. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B)
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (F : CanonicalGlobalCurrentCalculusInput)

theorem bassSerreShadowPushA_translate (γ : G) (v : G ⧸ A) (k : ℕ) (C : J.Current k) :
    (bassSerreShadowPushA T MA J IA F (γ • v)).push k ((regularSphereCurrentAction J F γ).push k C) =
      (bassSerreShadowPushA T MA J IA F v).push k C := by
  letI := MA.metric
  let act : RegularSphere G → RegularSphere G := fun u => γ • u
  let q := bassSerreQuotientShadowA T (γ • v)
  have hact := regularSphereActionLipschitz γ
  have hq : ∃ L : NNReal, LipschitzWith L q := ⟨_,bassSerreQuotientShadowA_lipschitz T MA (γ • v)⟩
  have hqv : ∃ L : NNReal, LipschitzWith L (bassSerreQuotientShadowA T v) :=
    ⟨_,bassSerreQuotientShadowA_lipschitz T MA v⟩
  have hcomp : ∃ L : NNReal, LipschitzWith L (q ∘ act) := by
    obtain ⟨L,hL⟩ := hq
    obtain ⟨K,hK⟩ := hact
    exact ⟨L*K,hL.comp hK⟩
  have he : q ∘ act = bassSerreQuotientShadowA T v :=
    funext (bassSerreQuotientShadowA_translate T γ v)
  exact (F.composition J J IA act q hact hq hcomp k C).trans
    (congrArg (fun h => h C) (globalCurrentPushforward_congr F J IA _ _ hcomp hqv he k))

theorem bassSerreShadowPushB_translate (γ : G) (v : G ⧸ B) (k : ℕ) (C : J.Current k) :
    (bassSerreShadowPushB T MB J IB F (γ • v)).push k ((regularSphereCurrentAction J F γ).push k C) =
      (bassSerreShadowPushB T MB J IB F v).push k C := by
  letI := MB.metric
  let act : RegularSphere G → RegularSphere G := fun u => γ • u
  let q := bassSerreQuotientShadowB T (γ • v)
  have hact := regularSphereActionLipschitz γ
  have hq : ∃ L : NNReal, LipschitzWith L q := ⟨_,bassSerreQuotientShadowB_lipschitz T MB (γ • v)⟩
  have hqv : ∃ L : NNReal, LipschitzWith L (bassSerreQuotientShadowB T v) :=
    ⟨_,bassSerreQuotientShadowB_lipschitz T MB v⟩
  have hcomp : ∃ L : NNReal, LipschitzWith L (q ∘ act) := by
    obtain ⟨L,hL⟩ := hq
    obtain ⟨K,hK⟩ := hact
    exact ⟨L*K,hL.comp hK⟩
  have he : q ∘ act = bassSerreQuotientShadowB T v :=
    funext (bassSerreQuotientShadowB_translate T γ v)
  exact (F.composition J J IB act q hact hq hcomp k C).trans
    (congrArg (fun h => h C) (globalCurrentPushforward_congr F J IB _ _ hcomp hqv he k))

theorem bassSerreRawTransferA_translate (Faithful : CurrentMassFaithfulnessInput IA)
    (γ : G) (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+1)) :
    bassSerreRawTransferA T MA J IA F Faithful k (finiteCoordinateCurrentAction J F γ (k+1) C) =
      bassSerreRawTransferA T MA J IA F Faithful k C := by
  have he : bassSerreShadowFamilyA T MA J IA F Faithful k (finiteCoordinateCurrentAction J F γ (k+1) C) =
      Finsupp.equivMapDomain (MulAction.toPerm γ) (bassSerreShadowFamilyA T MA J IA F Faithful k C) := by
    ext v
    obtain ⟨w,rfl⟩ := (MulAction.toPerm γ).surjective v
    change (bassSerreShadowPushA T MA J IA F (γ • w)).push (k+1)
      ((regularSphereCurrentAction J F γ).push (k+1) C.val) = _
    simpa only [Finsupp.equivMapDomain_apply,Equiv.symm_apply_apply] using
      bassSerreShadowPushA_translate T MA J IA F γ w (k+1) C.val
  change (bassSerreShadowFamilyA T MA J IA F Faithful k (finiteCoordinateCurrentAction J F γ (k+1) C)).sum
    (fun _ m => m) = (bassSerreShadowFamilyA T MA J IA F Faithful k C).sum (fun _ m => m)
  rw [he,Finsupp.sum_equivMapDomain]

theorem bassSerreRawTransferB_translate (Faithful : CurrentMassFaithfulnessInput IB)
    (γ : G) (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+1)) :
    bassSerreRawTransferB T MB J IB F Faithful k (finiteCoordinateCurrentAction J F γ (k+1) C) =
      bassSerreRawTransferB T MB J IB F Faithful k C := by
  have he : bassSerreShadowFamilyB T MB J IB F Faithful k (finiteCoordinateCurrentAction J F γ (k+1) C) =
      Finsupp.equivMapDomain (MulAction.toPerm γ) (bassSerreShadowFamilyB T MB J IB F Faithful k C) := by
    ext v
    obtain ⟨w,rfl⟩ := (MulAction.toPerm γ).surjective v
    change (bassSerreShadowPushB T MB J IB F (γ • w)).push (k+1)
      ((regularSphereCurrentAction J F γ).push (k+1) C.val) = _
    simpa only [Finsupp.equivMapDomain_apply,Equiv.symm_apply_apply] using
      bassSerreShadowPushB_translate T MB J IB F γ w (k+1) C.val
  change (bassSerreShadowFamilyB T MB J IB F Faithful k (finiteCoordinateCurrentAction J F γ (k+1) C)).sum
    (fun _ m => m) = (bassSerreShadowFamilyB T MB J IB F Faithful k C).sum (fun _ m => m)
  rw [he,Finsupp.sum_equivMapDomain]

end Paper28
