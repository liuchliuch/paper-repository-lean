import Paper28.BassSerreHullArea
import Paper28.CurrentFiniteMassBounds

/-! Concrete raw transfer mass bound. The actual finite sums are extended
by zero to the explicit hull, split into the two vertex types, and bounded
by the native joint area theorem. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Set
open scoped Classical
variable {G : Type} [Group G] [DecidableEq G] [Countable G] {A B : Subgroup G}
  (T : BassSerreObject A B)
  (MA : SphericalQuotientMetricInput A) (MB : SphericalQuotientMetricInput B)
  (J : CompactIntegralCurrentAlgebraInput.{0,0} (RegularSphere G) inferInstance)
  (IA : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient A) MA.metric)
  (IB : CompactIntegralCurrentAlgebraInput.{0,0} (RegularOrbitQuotient B) MB.metric)
  (F : CanonicalGlobalCurrentCalculusInput)

theorem bassSerreRawTransferA_hull_sum (Faithful : CurrentMassFaithfulnessInput IA)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+1)) (E : Finset G)
    (hE : J.support C.val ⊆ regularCoordinateSphere E) :
    bassSerreRawTransferA T MA J IA F Faithful k C =
      ∑ v ∈ (bassSerreHullVertices T E).toLeft, (bassSerreShadowPushA T MA J IA F v).push (k+1) C.val := by
  have hs : (bassSerreShadowFamilyA T MA J IA F Faithful k C).support ⊆ (bassSerreHullVertices T E).toLeft := by
    intro v hv
    apply Finset.mem_toLeft.mpr
    by_contra h
    obtain ⟨c,hc⟩ := bassSerreQuotientShadowA_outside_hull T E v h
    have hz := globalCurrentPushforward_constant_zero (bassSerreShadowPushA T MA J IA F v) Faithful k C.val c
      (fun u hu => hc u (hE hu))
    exact (Finsupp.mem_support_iff.mp hv) hz
  exact Finsupp.sum_of_support_subset _ hs (fun _ C => C) (fun _ _ => rfl)

theorem bassSerreRawTransferB_hull_sum (Faithful : CurrentMassFaithfulnessInput IB)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+1)) (E : Finset G)
    (hE : J.support C.val ⊆ regularCoordinateSphere E) :
    bassSerreRawTransferB T MB J IB F Faithful k C =
      ∑ v ∈ (bassSerreHullVertices T E).toRight, (bassSerreShadowPushB T MB J IB F v).push (k+1) C.val := by
  have hs : (bassSerreShadowFamilyB T MB J IB F Faithful k C).support ⊆ (bassSerreHullVertices T E).toRight := by
    intro v hv
    apply Finset.mem_toRight.mpr
    by_contra h
    obtain ⟨c,hc⟩ := bassSerreQuotientShadowB_outside_hull T E v h
    have hz := globalCurrentPushforward_constant_zero (bassSerreShadowPushB T MB J IB F v) Faithful k C.val c
      (fun u hu => hc u (hE hu))
    exact (Finsupp.mem_support_iff.mp hv) hz
  exact Finsupp.sum_of_support_subset _ hs (fun _ C => C) (fun _ _ => rfl)

theorem bassSerreRawTransfer_joint_mass
    (FaithfulA : CurrentMassFaithfulnessInput IA) (FaithfulB : CurrentMassFaithfulnessInput IB)
    (Area : FiniteCoordinateCurrentAreaInput J) (Fischer : FischerInput)
    (k : ℕ) (hk : 4 ≤ k+1) (C : finiteCoordinateSupportedCurrents J (k+1)) :
    IA.mass (bassSerreRawTransferA T MA J IA F FaithfulA k C)+
      IB.mass (bassSerreRawTransferB T MB J IB F FaithfulB k C) ≤ J.mass C.val := by
  obtain ⟨E,hE⟩ := C.property
  rw [bassSerreRawTransferA_hull_sum T MA J IA F FaithfulA k C E hE,
    bassSerreRawTransferB_hull_sum T MB J IB F FaithfulB k C E hE]
  let m : BassSerreVertex A B → ℝ := Sum.elim
    (fun a : G ⧸ A => IA.mass ((bassSerreShadowPushA T MA J IA F a).push (k+1) C.val))
    (fun b : G ⧸ B => IB.mass ((bassSerreShadowPushB T MB J IB F b).push (k+1) C.val))
  calc
    _ ≤ (∑ a ∈ (bassSerreHullVertices T E).toLeft, m (.inl a))+
        ∑ b ∈ (bassSerreHullVertices T E).toRight, m (.inr b) :=
      add_le_add (current_mass_finset_sum_le IA _ _) (current_mass_finset_sum_le IB _ _)
    _ = ∑ v ∈ bassSerreHullVertices T E, m v :=
      (Finset.sum_sum_eq_sum_toLeft_add_sum_toRight _ m).symm
    _ = ∑ v : BassSerreHullVertex T E, m v.val := (Finset.sum_attach _ m).symm
    _ ≤ J.mass C.val := bassSerre_hull_joint_area T MA MB J IA IB F Area Fischer E (k+1) hk C.val hE

end Paper28
