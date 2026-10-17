import Paper38.GaussianEnergyFacts
import Paper38.GradientWithin
noncomputable section
set_option maxHeartbeats 300000
set_option diagnostics false
namespace Paper38.GaussianGradientFlow
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius
open Set Real
open Model HilbertCoordinates

/-- Lemma 5.1's analytic conclusion for actual Gaussian symmetric-coordinate
solutions, from the original source hypotheses. Every constant is constructed. -/
theorem semiglobal {d : ℕ} {V : Model.E d → ℝ} {α β R : ℝ}
    (hV : AdmissiblePotential V α β) (hR : 0 ≤ R) {z : Tangent d}
    (hz : z ∈ Domain d)
    (hmin : ∀ x ∈ Domain d, HilbertCoordinates.energy V z ≤ HilbertCoordinates.energy V x) :
    ∃ S > 0, ∃ T ≥ 0, ∃ k > 0, ∀ q r : ℝ → Tangent d,
      (∀ s, 0 ≤ s → HasDerivAt q (field V (q s)) s) →
      (∀ s, 0 ≤ s → HasDerivAt r (field V (r s)) s) →
      (∀ s, 0 ≤ s → q s ∈ Domain d) → (∀ s, 0 ≤ s → r s ∈ Domain d) →
      HilbertCoordinates.energy V (q 0)-HilbertCoordinates.energy V z ≤ R →
      HilbertCoordinates.energy V (r 0)-HilbertCoordinates.energy V z ≤ R →
      (∀ t, 0 ≤ t → ‖q t-r t‖ ≤ S * ‖q 0-r 0‖) ∧
      (∀ t, T ≤ t → ‖q t-r t‖ ≤ S * exp (-k/2 * (t-T)) * ‖q 0-r 0‖) := by
  have a := @GradientStability.semiglobal (Tangent d) inferInstance inferInstance inferInstance
  have b := a (F := HilbertCoordinates.energy V) (P := HilbertMobility.P (d := d))
    (Ω := Domain d) (α := α) (R := R)
  have c := b hV.alpha_pos hR (Domain_isOpen d) (Domain_convex d)
  have e := c (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
  have f := e (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq)
  have g := f (HilbertMobility.P_contDiffOn (d := d) 1)
  have h := g (fun q hq v hv => HilbertMobility.P_quadratic_pos (d := d) q v hq hv)
  obtain ⟨S,hS,T,hT,k,hk,hs⟩ := h (sublevel_isCompact hV) hz hmin
  refine ⟨S,hS,T,hT,k,hk,?_⟩
  intro q r hq hr hqΩ hrΩ hqi hri
  exact hs q r hq hr hqΩ hrΩ hqi hri

/-- The same actual semiglobal theorem with exactly the source's right-domain
ODE derivative convention, without a negative-time extension assumption. -/
theorem semiglobal_within {d : ℕ} {V : Model.E d → ℝ} {α β R : ℝ}
    (hV : AdmissiblePotential V α β) (hR : 0 ≤ R) {z : Tangent d}
    (hz : z ∈ Domain d)
    (hmin : ∀ x ∈ Domain d, HilbertCoordinates.energy V z ≤ HilbertCoordinates.energy V x) :
    ∃ S > 0, ∃ T ≥ 0, ∃ k > 0, ∀ q r : ℝ → Tangent d,
      (∀ s, 0 ≤ s → HasDerivWithinAt q (field V (q s)) (Ici 0) s) →
      (∀ s, 0 ≤ s → HasDerivWithinAt r (field V (r s)) (Ici 0) s) →
      (∀ s, 0 ≤ s → q s ∈ Domain d) → (∀ s, 0 ≤ s → r s ∈ Domain d) →
      HilbertCoordinates.energy V (q 0)-HilbertCoordinates.energy V z ≤ R →
      HilbertCoordinates.energy V (r 0)-HilbertCoordinates.energy V z ≤ R →
      (∀ t, 0 ≤ t → ‖q t-r t‖ ≤ S*‖q 0-r 0‖) ∧
      (∀ t, T ≤ t → ‖q t-r t‖ ≤ S*exp (-k/2*(t-T))*‖q 0-r 0‖) := by
  have a := @GradientWithin.semiglobal (Tangent d) inferInstance inferInstance inferInstance
  have b := a (F := HilbertCoordinates.energy V) (P := HilbertMobility.P (d := d))
    (Ω := Domain d) (α := α) (R := R)
  have c := b hV.alpha_pos hR (Domain_isOpen d) (Domain_convex d)
  have e := c (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
  have f := e (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq)
  have g := f (HilbertMobility.P_contDiffOn (d := d) 1)
  have h := g (fun q hq v hv => HilbertMobility.P_quadratic_pos (d := d) q v hq hv)
  obtain ⟨S,hS,T,hT,k,hk,hs⟩ := h (sublevel_isCompact hV) hz hmin
  refine ⟨S,hS,T,hT,k,hk,?_⟩
  intro q r hq hr hqΩ hrΩ hqi hri
  exact hs q r hq hr hqΩ hrΩ hqi hri

end Paper38.GaussianGradientFlow
