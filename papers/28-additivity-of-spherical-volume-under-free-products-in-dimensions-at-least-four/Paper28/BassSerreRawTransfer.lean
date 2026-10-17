import Paper28.BassSerreShadowEquivariance
import Paper28.FiniteCoordinateCurrentGroup
import Mathlib.Algebra.BigOperators.Finsupp.Basic

/-! Actual finite integral shadow sums on finite-coordinate supported
sphere currents. Finiteness follows from the native explicit tree hull
and constant-map vanishing. Summation keeps every vertex and its integer
multiplicity. Descent to quotient polyhedral currents is a separate proof.
-/
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

def bassSerreShadowPushA (v : G ⧸ A) :
    GlobalCurrentPushforwardInput inferInstance MA.metric J IA (bassSerreQuotientShadowA T v) := by
  letI := MA.metric
  exact F.map J IA _ ⟨_,bassSerreQuotientShadowA_lipschitz T MA v⟩

def bassSerreShadowPushB (v : G ⧸ B) :
    GlobalCurrentPushforwardInput inferInstance MB.metric J IB (bassSerreQuotientShadowB T v) := by
  letI := MB.metric
  exact F.map J IB _ ⟨_,bassSerreQuotientShadowB_lipschitz T MB v⟩

theorem bassSerreShadowPushA_finite_support (Faithful : CurrentMassFaithfulnessInput IA)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+1)) :
    (Function.support (fun v : G ⧸ A => (bassSerreShadowPushA T MA J IA F v).push (k+1) C.val)).Finite := by
  obtain ⟨E,hE⟩ := C.property
  apply ((bassSerreHullVertices T E).finite_toSet.preimage Sum.inl_injective.injOn).subset
  intro v hv
  by_contra h
  obtain ⟨c,hc⟩ := bassSerreQuotientShadowA_outside_hull T E v h
  exact hv (globalCurrentPushforward_constant_zero (bassSerreShadowPushA T MA J IA F v)
    Faithful k C.val c (fun u hu => hc u (hE hu)))

theorem bassSerreShadowPushB_finite_support (Faithful : CurrentMassFaithfulnessInput IB)
    (k : ℕ) (C : finiteCoordinateSupportedCurrents J (k+1)) :
    (Function.support (fun v : G ⧸ B => (bassSerreShadowPushB T MB J IB F v).push (k+1) C.val)).Finite := by
  obtain ⟨E,hE⟩ := C.property
  apply ((bassSerreHullVertices T E).finite_toSet.preimage Sum.inr_injective.injOn).subset
  intro v hv
  by_contra h
  obtain ⟨c,hc⟩ := bassSerreQuotientShadowB_outside_hull T E v h
  exact hv (globalCurrentPushforward_constant_zero (bassSerreShadowPushB T MB J IB F v)
    Faithful k C.val c (fun u hu => hc u (hE hu)))

def bassSerreShadowFamilyA (Faithful : CurrentMassFaithfulnessInput IA) (k : ℕ) :
    finiteCoordinateSupportedCurrents J (k+1) →+ ((G ⧸ A) →₀ IA.Current (k+1)) where
  toFun C := Finsupp.ofSupportFinite _ (bassSerreShadowPushA_finite_support T MA J IA F Faithful k C)
  map_zero' := by
    ext v
    exact (bassSerreShadowPushA T MA J IA F v).push (k+1) |>.map_zero
  map_add' C D := by
    ext v
    exact (bassSerreShadowPushA T MA J IA F v).push (k+1) |>.map_add C.val D.val

def bassSerreShadowFamilyB (Faithful : CurrentMassFaithfulnessInput IB) (k : ℕ) :
    finiteCoordinateSupportedCurrents J (k+1) →+ ((G ⧸ B) →₀ IB.Current (k+1)) where
  toFun C := Finsupp.ofSupportFinite _ (bassSerreShadowPushB_finite_support T MB J IB F Faithful k C)
  map_zero' := by
    ext v
    exact (bassSerreShadowPushB T MB J IB F v).push (k+1) |>.map_zero
  map_add' C D := by
    ext v
    exact (bassSerreShadowPushB T MB J IB F v).push (k+1) |>.map_add C.val D.val

def bassSerreRawTransferA (Faithful : CurrentMassFaithfulnessInput IA) (k : ℕ) :
    finiteCoordinateSupportedCurrents J (k+1) →+ IA.Current (k+1) :=
  (Finsupp.liftAddHom (fun _ : G ⧸ A => AddMonoidHom.id (IA.Current (k+1)))).comp
    (bassSerreShadowFamilyA T MA J IA F Faithful k)

def bassSerreRawTransferB (Faithful : CurrentMassFaithfulnessInput IB) (k : ℕ) :
    finiteCoordinateSupportedCurrents J (k+1) →+ IB.Current (k+1) :=
  (Finsupp.liftAddHom (fun _ : G ⧸ B => AddMonoidHom.id (IB.Current (k+1)))).comp
    (bassSerreShadowFamilyB T MB J IB F Faithful k)

end Paper28
