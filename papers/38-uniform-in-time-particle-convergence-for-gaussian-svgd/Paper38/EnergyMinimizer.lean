import Paper38.EnergyCompactness
import Paper38.Specification

/-! Construct the actual reverse-KL Gaussian minimizer from its proved geometry. -/

noncomputable section
namespace Paper38.EnergyMinimizer

open Set
open scoped Matrix
open Paper38.Model

/-- Compact actual Gaussian sublevels construct an intrinsic critical point and
the unique minimizer of the literal source energy, transported back to the Model.
There is no minimizer or stationarity hypothesis. -/
theorem exists_unique_minimizer_from_geometry {d : ℕ} {V : E d → ℝ} {α β : ℝ}
    (hV : AdmissiblePotential V α β)
    (hC2 : ContDiffOn ℝ 2 (HilbertCoordinates.energy V) (HilbertCoordinates.Domain d))
    (hH : ∀ q ∈ HilbertCoordinates.Domain d, ∀ v : HilbertCoordinates.Tangent d,
      α * ‖v‖^2 ≤ (fderiv ℝ (fderiv ℝ (HilbertCoordinates.energy V)) q v) v) :
    ∃ z : HilbertCoordinates.Tangent d, z ∈ HilbertCoordinates.Domain d ∧
      gradient (HilbertCoordinates.energy V) z = 0 ∧
      Specification.IsUniqueMinimizer V (HilbertCoordinates.toModel d z) := by
  let F := HilbertCoordinates.energy V
  let Ω := HilbertCoordinates.Domain d
  have hstrong : EnergyDecay.StrongConvexGradientOn F (gradient F) Ω α :=
    GradientGeometry.strongConvexGradientOn_of_second_fderiv_lower
      (HilbertCoordinates.Domain_isOpen d) (HilbertCoordinates.Domain_convex d) hC2 hH
  have hcompact := EnergyCompactness.gaussian_energy_sublevel_compact_from_geometry hV hC2 hH
    (F (HilbertCoordinates.anchor d))
  obtain ⟨z, hz, hmin⟩ := GradientGeometry.exists_minimizer_of_compact_sublevel
    (HilbertCoordinates.anchor_mem_Domain d) hC2.continuousOn hcompact
  have hcrit := GradientGeometry.gradient_eq_zero_of_minimizer
    (HilbertCoordinates.Domain_isOpen d) hz hmin
  have hmodelmin : Specification.IsMinimizer V (HilbertCoordinates.toModel d z) := by
    refine ⟨hz, ?_⟩
    intro q hq
    have hsym : q.2ᵀ = q.2 := by simpa using hq.1
    let y := HilbertCoordinates.ofModel q hsym
    have hy : y ∈ HilbertCoordinates.Domain d := by
      simpa [y, HilbertCoordinates.Domain, Model.domain] using hq
    simpa [HilbertCoordinates.energy, y] using hmin y hy
  refine ⟨z, hz, hcrit, hmodelmin, ?_⟩
  intro q hq
  have hsym : q.2ᵀ = q.2 := by simpa using hq.1.1
  let y := HilbertCoordinates.ofModel q hsym
  have hy : y ∈ HilbertCoordinates.Domain d := by
    simpa [y, HilbertCoordinates.Domain, Model.domain] using hq.1
  have hle : F y ≤ F z := by
    simpa [F, HilbertCoordinates.energy, y] using hq.2 (HilbertCoordinates.toModel d z) hz
  have heq : F y = F z := le_antisymm hle (hmin y hy)
  have hyz := GradientGeometry.unique_of_strongConvex_critical hV.alpha_pos hstrong hz hy hcrit heq
  have hraw := congrArg (HilbertCoordinates.toModel d) hyz
  simpa only [y, HilbertCoordinates.toModel_ofModel] using hraw

end Paper38.EnergyMinimizer
