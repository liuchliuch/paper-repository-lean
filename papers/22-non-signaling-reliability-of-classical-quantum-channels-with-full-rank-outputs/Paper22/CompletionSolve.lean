import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Paper22.Basic

/-! The Banach fixed point step of effect completion, on actual Hermitian matrices. -/
open scoped MatrixOrder ComplexOrder Matrix.Norms.L2Operator
open Matrix
noncomputable section
namespace Paper22

/-- Solving a real linear perturbation of the identity on Hermitian matrices.
The distance bound is obtained from the convergent contraction iteration. -/
theorem completion_linear_solve {d : ℕ}
    (Φ : Matrix (Fin d) (Fin d) ℂ →ₗ[ℝ] Matrix (Fin d) (Fin d) ℂ)
    (hΦ : ∀ X, IsSelfAdjoint X → IsSelfAdjoint (Φ X))
    (c : ℝ) (hc0 : 0 ≤ c) (hc1 : c < 1)
    (hbound : ∀ X, IsSelfAdjoint X → ‖X - Φ X‖ ≤ c * ‖X‖)
    (H : Matrix (Fin d) (Fin d) ℂ) (hH : IsSelfAdjoint H) :
    ∃ X : Matrix (Fin d) (Fin d) ℂ,
      IsSelfAdjoint X ∧ Φ X = H ∧ ‖X - H‖ ≤ c * ‖H‖ / (1 - c) := by
  have hclosed : IsClosed (selfAdjoint (Matrix (Fin d) (Fin d) ℂ) : Set (Matrix (Fin d) (Fin d) ℂ)) := by
    change IsClosed {X : Matrix (Fin d) (Fin d) ℂ | star X = X}
    exact isClosed_eq continuous_star continuous_id
  letI : CompleteSpace (selfAdjoint (Matrix (Fin d) (Fin d) ℂ)) :=
    hclosed.isComplete.completeSpace_coe
  let f : selfAdjoint (Matrix (Fin d) (Fin d) ℂ) →
      selfAdjoint (Matrix (Fin d) (Fin d) ℂ) :=
    fun X => ⟨H + ((X : Matrix (Fin d) (Fin d) ℂ) - Φ X), hH.add (X.prop.sub (hΦ _ X.prop))⟩
  have hcontract : ContractingWith ⟨c, hc0⟩ f := by
    refine ⟨hc1, LipschitzWith.of_dist_le_mul ?_⟩
    intro X Y
    rw [dist_eq_norm, dist_eq_norm]
    change ‖(H + ((X : Matrix (Fin d) (Fin d) ℂ) - Φ X)) -
      (H + ((Y : Matrix (Fin d) (Fin d) ℂ) - Φ Y))‖ ≤ c * ‖((X - Y : selfAdjoint _) : Matrix (Fin d) (Fin d) ℂ)‖
    have heq : (H + ((X : Matrix (Fin d) (Fin d) ℂ) - Φ X)) -
        (H + ((Y : Matrix (Fin d) (Fin d) ℂ) - Φ Y)) =
        ((X : Matrix (Fin d) (Fin d) ℂ) - Y) - Φ ((X : Matrix (Fin d) (Fin d) ℂ) - Y) := by
      rw [map_sub]
      abel
    rw [heq]
    exact hbound _ (X.prop.sub Y.prop)
  let X := hcontract.fixedPoint f
  have hfix : f X = X := hcontract.fixedPoint_isFixedPt
  have hfix' : H + ((X : Matrix (Fin d) (Fin d) ℂ) - Φ X) = X :=
    congrArg Subtype.val hfix
  have hsolve : Φ X = H := by
    apply sub_eq_zero.mp
    calc Φ X - H = (X : Matrix (Fin d) (Fin d) ℂ) -
        (H + ((X : Matrix (Fin d) (Fin d) ℂ) - Φ X)) := by abel
      _ = 0 := by rw [hfix']; exact sub_self _
  refine ⟨X, X.prop, hsolve, ?_⟩
  have hd := hcontract.dist_fixedPoint_le (⟨H, hH⟩ : selfAdjoint _)
  rw [dist_eq_norm, dist_eq_norm] at hd
  have hdist : ‖(X : Matrix (Fin d) (Fin d) ℂ) - H‖ ≤ ‖H - Φ H‖ / (1 - c) := by
    change ‖H - (X : Matrix (Fin d) (Fin d) ℂ)‖ ≤
      ‖H - (H + (H - Φ H))‖ / (1 - c) at hd
    have heq : H - (H + (H - Φ H)) = -(H - Φ H) := by abel
    rw [heq, norm_neg] at hd
    calc ‖(X : Matrix (Fin d) (Fin d) ℂ) - H‖ = ‖H - (X : Matrix (Fin d) (Fin d) ℂ)‖ := norm_sub_rev _ _
      _ ≤ _ := hd
  exact hdist.trans (div_le_div_of_nonneg_right (hbound H hH) (sub_nonneg.mpr hc1.le))

end Paper22
