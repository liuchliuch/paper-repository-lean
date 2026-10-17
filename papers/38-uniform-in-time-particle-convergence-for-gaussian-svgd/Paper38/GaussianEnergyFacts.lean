import Paper38.GlobalODE
import Paper38.GradientWithin
import Paper38.EnergyMinimizer
import Paper38.HilbertMobility
import Paper38.GaussianEnergyGeometry

/-! Actual Gaussian symmetric-coordinate energy, minimizer and global gradient flow. -/
noncomputable section
set_option maxHeartbeats 2000000
namespace Paper38.GaussianGradientFlow
open Set Real
open Model HilbertCoordinates

/-- The actual square-root-coordinate preconditioned gradient field (4.10). -/
def field {d : ℕ} (V : Model.E d → ℝ) (q : Tangent d) : Tangent d :=
  -(HilbertMobility.P q (gradient (HilbertCoordinates.energy V) q))

/-- Compactness of actual Gaussian energy sublevels, from the original potential
hypotheses alone. It includes exclusion of the positive-definite boundary. -/
theorem sublevel_isCompact {d : ℕ} {V : Model.E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) (c : ℝ) :
    IsCompact {q : Tangent d | q ∈ Domain d ∧ HilbertCoordinates.energy V q ≤ c} := by
  exact EnergyCompactness.gaussian_energy_sublevel_compact_from_geometry hV
    (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
    (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq) c

/-- The actual source energy is strongly convex in its intrinsic Riesz-gradient
coordinates, from the original potential assumptions alone. -/
theorem strongly_convex {d : ℕ} {V : Model.E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) :
    EnergyDecay.StrongConvexGradientOn (HilbertCoordinates.energy V)
      (gradient (HilbertCoordinates.energy V)) (Domain d) α := by
  exact GradientGeometry.strongConvexGradientOn_of_second_fderiv_lower
    (Domain_isOpen d) (Domain_convex d) (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
    (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq)

/-- The unique minimizer in Lemma 4.2 is constructed in the literal Model energy;
no minimizer, gradient stationarity or coercivity assumption is added. -/
theorem exists_unique_minimizer {d : ℕ} {V : Model.E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) :
    ∃ z : Tangent d, z ∈ Domain d ∧ gradient (HilbertCoordinates.energy V) z = 0 ∧
      Specification.IsUniqueMinimizer V (toModel d z) := by
  exact EnergyMinimizer.exists_unique_minimizer_from_geometry hV
    (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
    (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq)

/-- `C¹` regularity of the actual intrinsic Gaussian field; no third derivative
of the source potential is used. -/
theorem field_contDiffOn {d : ℕ} {V : Model.E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β) : ContDiffOn ℝ 1 (field V) (Domain d) :=
  ((HilbertMobility.P_contDiffOn (d := d) 1).clm_apply
    (GradientGeometry.gradient_contDiffOn (Domain_isOpen d)
      (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV))).neg

/-- Construct the global actual Gaussian gradient flow, its unique reverse-KL
minimizer, exponential convergence and trajectory uniqueness. The explicit
external dependency is only the standard maximal-ODE continuation theorem. -/
theorem exists_unique_global_flow {d : ℕ}
    (hstandard : GlobalODE.StandardMaximalODETheorem (Tangent d))
    {V : Model.E d → ℝ} {α β : ℝ} (hV : AdmissiblePotential V α β)
    {x₀ : Tangent d} (hx₀ : x₀ ∈ Domain d) :
    ∃ z ∈ Domain d,
      (∀ x ∈ Domain d, HilbertCoordinates.energy V z ≤ HilbertCoordinates.energy V x) ∧
      gradient (HilbertCoordinates.energy V) z = 0 ∧
    ∃ p > 0, ∃ q : ℝ → Tangent d, q 0 = x₀ ∧
      (∀ t : ℝ, 0 ≤ t → q t ∈ Domain d ∧ HasDerivAt q (field V (q t)) t ∧
        HilbertCoordinates.energy V (q t)-HilbertCoordinates.energy V z ≤
          (HilbertCoordinates.energy V x₀-HilbertCoordinates.energy V z) * exp (-2*α*p*t) ∧
        ‖q t-z‖ ≤ sqrt (2*(HilbertCoordinates.energy V x₀-HilbertCoordinates.energy V z)/α) * exp (-α*p*t)) ∧
      (∀ r : ℝ → Tangent d, r 0 = x₀ → (∀ t, 0 ≤ t → r t ∈ Domain d) →
        (∀ t, 0 ≤ t → HasDerivAt r (field V (r t)) t) → ∀ t, 0 ≤ t → r t = q t) := by
  exact GlobalODE.exists_unique_global_C2_gradient_flow (F := HilbertCoordinates.energy V) (P := HilbertMobility.P (d := d)) hstandard hV.alpha_pos
    (Domain_isOpen d) (Domain_convex d) (GaussianEnergyGeometry.intrinsic_energy_contDiffOn hV)
    (fun q hq v => GaussianEnergyGeometry.intrinsic_energy_second_fderiv_lower hV q v hq)
    (HilbertMobility.P_contDiffOn (d := d) 1)
    (fun q hq v hv => HilbertMobility.P_quadratic_pos (d := d) q v hq hv)
    (sublevel_isCompact hV) hx₀

end Paper38.GaussianGradientFlow
