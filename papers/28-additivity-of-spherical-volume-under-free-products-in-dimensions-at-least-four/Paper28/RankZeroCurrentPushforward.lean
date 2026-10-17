import Paper28.RankDeficientJacobian
import Paper28.CurrentLocalityInputs
import Paper28.EuclideanAreaInput

/-! A strictly lower dimensional actual tangent differential gives the
zero pushed current. The rank, Gram vanishing and area argument are own
proofs; the only inputs are generic area/locality and mass faithfulness. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open MeasureTheory Set
universe w v

theorem push_eq_zero_of_stratified_tangent_rank
    {Y : Type w} (metricY : MetricSpace Y) {d m k : ℕ}
    (I : CompactIntegralCurrentAlgebraInput.{0,v} (EuclideanAmbient d) inferInstance)
    (R : EuclideanCurrentTangentInput d I)
    (J : CompactIntegralCurrentAlgebraInput.{w,v} Y metricY)
    (hFaith : CurrentMassFaithfulnessInput J) (hCB : CauchyBinetInput)
    (U : Set (EuclideanAmbient d)) (f : EuclideanAmbient d → Y) (hU : IsOpen U)
    (hf : LipschitzNearSet inferInstance metricY f U)
    (P : NeighborhoodCurrentPushforwardInput inferInstance metricY I J U f hU hf)
    (A : EuclideanCurrentAreaInput metricY I R J U f hU hf P)
    (C : supportedCurrents I U k) (hk : 0 < k)
    {Face : Type*} [Fintype Face] (strata : Face → Set (EuclideanAmbient d))
    (g : EuclideanAmbient d → EuclideanAmbient m)
    (D : EuclideanAmbient d → Matrix (Fin m) (Fin d) ℝ)
    (hCover : I.support C.val ⊆ ⋃ l, strata l)
    (hUnit : ∀ l x, x ∈ strata l → ‖g x‖ = 1)
    (hRound : ∀ l, RoundLiftOn metricY f g (strata l))
    (hSmooth : ∀ l x, x ∈ strata l → HasFDerivAt g (Matrix.toEuclideanLin (D x)).toContinuousLinearMap x)
    (S : Submodule ℝ (EuclideanAmbient d))
    (hTangent : ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), R.plane C.val x ≤ S)
    (W : EuclideanAmbient d → Submodule ℝ (EuclideanAmbient m))
    (hW : ∀ x ∈ I.support C.val, Module.finrank ℝ (W x) < k)
    (hD : ∀ x ∈ I.support C.val, ∀ h ∈ S, Matrix.toEuclideanLin (D x) h ∈ W x) :
    P.push k C = 0 := by
  have hJac := metricJacobian_on_piece_of_finite_strata metricY I R J U f hU hf P A C
    (I.support C.val) strata g D hCover hUnit hRound hSmooth
  have hZero : ∀ᵐ x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)), A.metricJacobian k C x = 0 := by
    filter_upwards [R.support_ae C.val,R.simple_tangent_ae C.val hk,hTangent,hJac] with x hx he hS hJ
    obtain ⟨e,_,hPolar,hSpan⟩ := he
    have heS : ∀ i, e i ∈ S := by
      intro i
      apply hS
      rw [← hSpan]
      exact Submodule.subset_span (mem_range_self i)
    rw [hJ hx,hPolar]
    exact exteriorJacobian_zero_of_subspace_dimension hCB (D x) e (W x) (hW x hx)
      (fun i => hD x hx (e i) (heS i))
  have hMass : J.mass (P.push k C) = 0 := by
    apply le_antisymm
    · calc
        _ ≤ ∫ x, A.metricJacobian k C x ∂(R.massMeasure C.val : Measure (EuclideanAmbient d)) := A.mass_area_le k C
        _ = 0 := by rw [integral_congr_ae hZero,integral_zero]
    · exact J.mass_nonneg _
  exact hFaith.eq_zero_of_mass_zero _ hMass

end Paper28
