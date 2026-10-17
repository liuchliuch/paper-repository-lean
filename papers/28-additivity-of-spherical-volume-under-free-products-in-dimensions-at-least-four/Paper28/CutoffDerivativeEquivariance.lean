import Paper28.CutoffDerivatives
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-! Equivariance of the actual cutoff derivatives and of their total norm.
The chain rule for a linear isometry equivalence holds even at nondifferentiable
points, so no unproved derivative transformation is postulated. -/
set_option autoImplicit false
noncomputable section
namespace Paper28
variable {G J : Type*} [Group G] [DecidableEq G] [Fintype J]
variable (c : J → CoordinateHilbert G) [∀ j, Fintype (regularStabilizer (c j))]
variable (b : ∀ j, ContDiffBump (c j))

theorem cutoffDerivative_equivariant (j : J) (γ δ : G) (u : CoordinateHilbert G) :
    (cutoffDerivative c b (j,δ*γ) (leftRegular δ u)).comp
      (leftRegular δ).toContinuousLinearEquiv.toContinuousLinearMap = cutoffDerivative c b (j,γ) u := by
  have he : normalizedCutoff c b (j,δ*γ) ∘ (leftRegular δ).toContinuousLinearEquiv =
      normalizedCutoff c b (j,γ) := funext (fun v => normalizedCutoff_equivariant c b j γ δ v)
  have h := (leftRegular δ).toContinuousLinearEquiv.comp_right_fderiv
    (f := normalizedCutoff c b (j,δ*γ)) (x := u)
  rw [he] at h
  exact h.symm

theorem cutoffDerivative_norm_equivariant (j : J) (γ δ : G) (u : CoordinateHilbert G) :
    ‖cutoffDerivative c b (j,δ*γ) (leftRegular δ u)‖ = ‖cutoffDerivative c b (j,γ) u‖ := by
  have hn := ContinuousLinearMap.opNorm_comp_linearIsometryEquiv
    (cutoffDerivative c b (j,δ*γ) (leftRegular δ u)) (leftRegular δ)
  change ‖(cutoffDerivative c b (j,δ*γ) (leftRegular δ u)).comp
    (leftRegular δ).toContinuousLinearEquiv.toContinuousLinearMap‖ = _ at hn
  rw [← hn,cutoffDerivative_equivariant]

theorem cutoffGradientSum_equivariant (δ : G) (u : CoordinateHilbert G) :
    cutoffGradientSum c b (leftRegular δ u) = cutoffGradientSum c b u := by
  let e : J×G ≃ J×G := Equiv.prodCongr (Equiv.refl J) (Equiv.mulLeft δ)
  unfold cutoffGradientSum
  calc
    _ = ∑' i : J×G, ‖cutoffDerivative c b (e i) (leftRegular δ u)‖ :=
      (e.tsum_eq (fun i => ‖cutoffDerivative c b i (leftRegular δ u)‖)).symm
    _ = _ := tsum_congr (fun i => cutoffDerivative_norm_equivariant c b i.1 i.2 δ u)

end Paper28
