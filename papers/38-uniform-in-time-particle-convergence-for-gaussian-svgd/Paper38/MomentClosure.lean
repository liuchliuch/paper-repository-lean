import Paper38.Mobility
import Paper38.EmpiricalCovarianceDynamics

/-!
# Exact projected-particle moment vector field

The coefficient is precisely the one in (2.5). The identities below connect the
usual affine moment derivative to the source moment field (2.3), without replacing
the particle system by a separately prescribed moment system.
-/

namespace Paper38.MomentClosure

open Matrix
open Paper38.Mobility

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- The actual common affine coefficient in the projected particle equation (2.5). -/
def projectedCoefficient (μ m : Vec d) (S Γ : Mat d) : Mat d :=
  1 - Γ * S - Matrix.vecMulVec m μ

/-- The affine mean derivative agrees with exactly (2.3a). -/
theorem affine_mean_eq_momentMean (μ m : Vec d) (S Γ : Mat d) :
    projectedCoefficient μ m S Γ *ᵥ μ - m = momentMean μ m S Γ := by
  simp only [projectedCoefficient, momentMean, Matrix.sub_mulVec,
    Matrix.vecMulVec_mulVec, op_smul_eq_smul]
  ext i
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The affine covariance derivative agrees with exactly (2.3b). -/
theorem affine_covariance_eq_momentCov (μ m : Vec d) (S Γ : Mat d)
    (hS : Sᵀ = S) (hΓ : Γᵀ = Γ) :
    projectedCoefficient μ m S Γ * S + S * (projectedCoefficient μ m S Γ)ᵀ =
      momentCov μ m S Γ := by
  simp only [projectedCoefficient, momentCov, Matrix.transpose_sub,
    Matrix.transpose_one, Matrix.transpose_mul, Matrix.transpose_vecMulVec,
    hS, hΓ, two_smul ℝ S]
  noncomm_ring

/-- The projected particle equation (2.5) gives exactly the empirical moment
ODE (2.3). This is the derivative-closure part of Lemma 6.1; no solution existence
or uniqueness assertion is included. -/
theorem projected_particle_moment_closure {N d : ℕ} (hN : 0 < N)
    (X : ℝ → Fin N → Fin d → ℝ) (t : ℝ) (m : Fin d → ℝ)
    (Γ : Matrix (Fin d) (Fin d) ℝ) (hΓ : Γᵀ = Γ)
    (hX : ∀ i, HasDerivAt (fun s => X s i)
      (projectedCoefficient (Paper38.Empirical.mean (X t)) m
        (Paper38.Empirical.covariance (X t)) Γ *ᵥ X t i - m) t) :
    HasDerivAt (fun s => Paper38.Empirical.mean (X s))
      (momentMean (Paper38.Empirical.mean (X t)) m
        (Paper38.Empirical.covariance (X t)) Γ) t ∧
    HasDerivAt (fun s => Paper38.Empirical.covariance (X s))
      (momentCov (Paper38.Empirical.mean (X t)) m
        (Paper38.Empirical.covariance (X t)) Γ) t := by
  have hS : (Paper38.Empirical.covariance (X t))ᵀ =
      Paper38.Empirical.covariance (X t) := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      (Paper38.Empirical.covariance_posSemidef (X t)).isHermitian.eq
  rcases Paper38.Empirical.affine_particle_moment_closure hN X t
    (projectedCoefficient (Paper38.Empirical.mean (X t)) m
      (Paper38.Empirical.covariance (X t)) Γ) m hX with ⟨hμ, hC⟩
  rw [affine_mean_eq_momentMean] at hμ
  rw [affine_covariance_eq_momentCov _ _ _ _ hS hΓ] at hC
  exact ⟨hμ, hC⟩

end Paper38.MomentClosure
