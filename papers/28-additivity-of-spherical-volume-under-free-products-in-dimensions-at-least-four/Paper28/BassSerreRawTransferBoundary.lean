import Paper28.BassSerreRawTransfer

/-! Positive-degree boundary commutation for the actual finite shadow
sums. Degree zero is never used. This precedes quotient presentation
descent and follows from the generic AK boundary formula term by term. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open scoped Classical

theorem finsupp_sum_addHom {V M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (h : M →+ N) (f : V →₀ M) :
    h (f.sum (fun _ m => m)) = (f.mapRange h h.map_zero).sum (fun _ n => n) := by
  rw [Finsupp.sum_mapRange_index (fun _ => rfl),map_finsuppSum]

variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B)
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (F : CanonicalGlobalCurrentCalculusInput)

theorem bassSerreRawTransferA_boundary (Faithful : CurrentMassFaithfulnessInput IA)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+2)) :
    IA.boundary (k+1) (bassSerreRawTransferA T MA J IA F Faithful (k+1) C) =
      bassSerreRawTransferA T MA J IA F Faithful k (finiteCoordinateBoundary J (k+1) C) := by
  have he : (bassSerreShadowFamilyA T MA J IA F Faithful (k+1) C).mapRange
      (IA.boundary (k+1)) (map_zero _) =
      bassSerreShadowFamilyA T MA J IA F Faithful k (finiteCoordinateBoundary J (k+1) C) := by
    ext v
    exact (bassSerreShadowPushA T MA J IA F v).boundary_comm (k+1) C.val
  change IA.boundary (k+1) ((bassSerreShadowFamilyA T MA J IA F Faithful (k+1) C).sum (fun _ m => m)) = _
  rw [finsupp_sum_addHom,he]
  rfl

theorem bassSerreRawTransferB_boundary (Faithful : CurrentMassFaithfulnessInput IB)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+2)) :
    IB.boundary (k+1) (bassSerreRawTransferB T MB J IB F Faithful (k+1) C) =
      bassSerreRawTransferB T MB J IB F Faithful k (finiteCoordinateBoundary J (k+1) C) := by
  have he : (bassSerreShadowFamilyB T MB J IB F Faithful (k+1) C).mapRange
      (IB.boundary (k+1)) (map_zero _) =
      bassSerreShadowFamilyB T MB J IB F Faithful k (finiteCoordinateBoundary J (k+1) C) := by
    ext v
    exact (bassSerreShadowPushB T MB J IB F v).boundary_comm (k+1) C.val
  change IB.boundary (k+1) ((bassSerreShadowFamilyB T MB J IB F Faithful (k+1) C).sum (fun _ m => m)) = _
  rw [finsupp_sum_addHom,he]
  rfl

end Paper28
