import Paper28.NeighborhoodPushforwardInput
import Paper28.StrictTangentMeasures
import Paper28.CompoundJacobian
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! Standard AK metric area and approximate-differential locality on actual
smooth round lifts. The metric Jacobian is an external canonical object;
its smooth-lift value is the actual Euclidean exterior/Gram Jacobian.
There is no incident maximum, retraction, approximation or sharp upper
mass statement among these generic calculus laws. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory Set
open scoped Topology
universe w v

def RoundLiftOn {Y : Type w} (metricY : MetricSpace Y) {d m : ℕ}
    (f : EuclideanAmbient d → Y) (g : EuclideanAmbient d → EuclideanSpace ℝ (Fin m))
    (A : Set (EuclideanAmbient d)) : Prop :=
  ∀ x ∈ A, ∃ r : ℝ, 0 < r ∧ ∀ y ∈ A, ∀ z ∈ A,
    dist y x < r → dist z x < r →
      @dist Y metricY.toDist (f y) (f z) = angular (g y) (g z)

structure EuclideanCurrentAreaInput {Y : Type w} (metricY : MetricSpace Y) {d : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf) where
  metricJacobian : ∀ k, supportedCurrents I U k → EuclideanAmbient d → ℝ
  jacobian_nonneg : ∀ k (C : supportedCurrents I U k) x, 0 ≤ metricJacobian k C x
  jacobian_integrable : ∀ k (C : supportedCurrents I U k),
    Integrable (metricJacobian k C) (R.massMeasure C.val : Measure (EuclideanAmbient d))
  mass_area_le : ∀ k (C : supportedCurrents I U k),
    J.mass (P.push k C) ≤ ∫ x, metricJacobian k C x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d))
  mass_area_eq_of_injective : ∀ k (C : supportedCurrents I U k), Set.InjOn f (I.support C.val) →
    J.mass (P.push k C) = ∫ x, metricJacobian k C x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d))
  smooth_round_lift_locality : ∀ k (C : supportedCurrents I U k) (m : ℕ)
    (A : Set (EuclideanAmbient d))
    (g : EuclideanAmbient d → EuclideanSpace ℝ (Fin m))
    (D : EuclideanAmbient d → Matrix (Fin m) (Fin d) ℝ),
    (∀ x ∈ A, ‖g x‖ = 1) → RoundLiftOn metricY f g A →
    (∀ x ∈ A, HasFDerivAt g (Matrix.toEuclideanLin (D x)).toContinuousLinearMap x) →
      ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), x ∈ A →
        metricJacobian k C x = exteriorJacobian (k := k) (D x) (R.polar C.val x)

/-- A closed incident piece may meet several image faces. The local metric
comparison is required only on their finitely many relative face strata;
finite locality then gives the Jacobian identity on the whole piece. -/
theorem metricJacobian_on_piece_of_finite_strata {Y : Type w} (metricY : MetricSpace Y) {d k m : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I) (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf)
    (A : EuclideanCurrentAreaInput metricY I R J U f hU hf P) (C : supportedCurrents I U k)
    {Face : Type*} [Fintype Face] (piece : Set (EuclideanAmbient d)) (strata : Face → Set (EuclideanAmbient d))
    (g : EuclideanAmbient d → EuclideanSpace ℝ (Fin m))
    (D : EuclideanAmbient d → Matrix (Fin m) (Fin d) ℝ)
    (hCover : piece ⊆ ⋃ l, strata l)
    (hUnit : ∀ l x, x ∈ strata l → ‖g x‖ = 1)
    (hRound : ∀ l, RoundLiftOn metricY f g (strata l))
    (hSmooth : ∀ l x, x ∈ strata l → HasFDerivAt g (Matrix.toEuclideanLin (D x)).toContinuousLinearMap x) :
    ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), x ∈ piece →
      A.metricJacobian k C x = exteriorJacobian (k := k) (D x) (R.polar C.val x) := by
  have h : ∀ l, ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), x ∈ strata l →
      A.metricJacobian k C x = exteriorJacobian (k := k) (D x) (R.polar C.val x) := fun l =>
    A.smooth_round_lift_locality k C m (strata l) g D (hUnit l) (hRound l) (hSmooth l)
  filter_upwards [ae_all_iff.mpr h] with x hx
  intro hxp
  obtain ⟨l,hl⟩ := mem_iUnion.mp (hCover hxp)
  exact hx l hl

end Paper28
