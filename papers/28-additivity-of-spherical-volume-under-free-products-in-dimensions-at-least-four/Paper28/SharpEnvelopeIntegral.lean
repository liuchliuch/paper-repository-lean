import Paper28.ExteriorIncidentEnvelope
import Paper28.WeakMeasureInputs

/-! The paper-owned sharp upper-integral step for incident retraction
Jacobians. The generic Portmanteau input is instantiated with the actual
bounded Gram/exterior envelope constructed here; its limiting value is
proved from the tangent Gram identity. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
open Filter MeasureTheory Set
open scoped Topology
variable {J : Type*} [Fintype J]

set_option maxHeartbeats 600000 in
theorem sharp_exterior_envelope_integral (hCB : CauchyBinetInput) (hPort : UpperPortmanteauInput.{0})
    {d k m0 : ℕ} (m : J → ℕ) (pieces : J → Set (EuclideanSpace ℝ (Fin d)))
    (D : ∀ j, EuclideanSpace ℝ (Fin d) → Matrix (Fin (m j)) (Fin d) ℝ)
    (D0 : EuclideanSpace ℝ (Fin d) → Matrix (Fin m0) (Fin d) ℝ)
    (hK : ∀ j, IsCompact (pieces j)) (hD : ∀ j, ContinuousOn (D j) (pieces j))
    (μi : ℕ → FiniteMeasure (EuclideanSpace ℝ (Fin d) × EuclideanExterior d k))
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d) × EuclideanExterior d k))
    (hWeak : Tendsto μi atTop (𝓝 μ))
    (hTangent : ∀ᵐ p ∂(μ : Measure (EuclideanSpace ℝ (Fin d) × EuclideanExterior d k)), ∃ e : Fin k → EuclideanSpace ℝ (Fin d),
      Orthonormal ℝ e ∧ p.2 = pluckerCoordinates e ∧ (∃ j, p.1 ∈ pieces j) ∧
        ∀ j, p.1 ∈ pieces j →
          Matrix.gram ℝ (fun i => Matrix.toEuclideanLin (D j p.1) (e i)) =
            Matrix.gram ℝ (fun i => Matrix.toEuclideanLin (D0 p.1) (e i))) :
    ∃ B : J → ℝ, (∀ j, 0 ≤ B j) ∧
      (∀ j, ∀ x ∈ pieces j, ∀ τ : EuclideanExterior d k, ‖τ‖ = 1 →
        exteriorJacobian (k := k) (D j x) τ ≤ B j) ∧
      (∀ᵐ p ∂(μ : Measure (EuclideanSpace ℝ (Fin d) × EuclideanExterior d k)), exteriorIncidentEnvelope (k := k) m pieces D B p = exteriorJacobian (k := k) (D0 p.1) p.2) ∧
      ∀ ε : ℝ, 0 < ε → ∀ᶠ i in atTop,
        (∫ p, exteriorIncidentEnvelope (k := k) m pieces D B p ∂(μi i : Measure (EuclideanSpace ℝ (Fin d) × EuclideanExterior d k))) ≤
          (∫ p, exteriorJacobian (k := k) (D0 p.1) p.2 ∂(μ : Measure (EuclideanSpace ℝ (Fin d) × EuclideanExterior d k)))+ε := by
  choose B hB hBound using fun j => exists_exteriorJacobian_bound (k := k) (pieces j) (hK j) (D j) (hD j)
  have hEq : ∀ᵐ p ∂(μ : Measure (EuclideanSpace ℝ (Fin d) × EuclideanExterior d k)),
      exteriorIncidentEnvelope (k := k) m pieces D B p = exteriorJacobian (k := k) (D0 p.1) p.2 := by
    filter_upwards [hTangent] with p hp
    obtain ⟨e,he,hpe,hSome,hGram⟩ := hp
    change exteriorIncidentEnvelope (k := k) m pieces D B (p.1,p.2) =
      exteriorJacobian (k := k) (D0 p.1) p.2
    rw [hpe]
    have hτ : ‖pluckerCoordinates e‖ = 1 := pluckerCoordinates_norm_of_orthonormal hCB e he
    exact (exteriorIncidentEnvelope_tangent_eq hCB m pieces D B p.1 e _ hSome hGram
      (fun j hj => hBound j p.1 hj _ hτ)).trans (exteriorJacobian_plucker hCB (D0 p.1) e).symm
  have hJ := exteriorIncidentEnvelope_upperSemicontinuous (k := k) m pieces D B (fun j => (hK j).isClosed) hD
  obtain ⟨M,hM⟩ := exteriorIncidentEnvelope_bounded (k := k) m pieces D B
  refine ⟨B,hB,hBound,hEq,?_⟩
  intro ε hε
  have h := hPort _ μi μ hWeak (exteriorIncidentEnvelope (k := k) m pieces D B) M hJ hM ε hε
  rwa [integral_congr_ae hEq] at h

end Paper28
