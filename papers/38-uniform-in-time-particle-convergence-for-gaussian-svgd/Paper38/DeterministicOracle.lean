import Paper38.AffineLifting
import Paper38.Specification
import Paper38.TransportParticleAffine

/-!
# Deterministic transport assembly for Theorem 2.1

These are component theorems. They prove the oracle transport estimate from an
actual affine representation, a bound on the actual moment discrepancy, and
an actual covariance eigenvalue bound. They do not replace the remaining ODE
existence/uniqueness and sublevel-geometry proof obligations of Theorem 2.1.
-/

noncomputable section
namespace Paper38.DeterministicOracle

open MeasureTheory Paper38.Model Paper38.Transport Paper38.AffineLifting
open scoped ENNReal NNReal

variable {d N : ℕ} [NeZero d]

/-- The exact transport assembly at one physical time. All three probability
laws are the actual laws from `Model`, and both couplings are genuine measures. -/
theorem fixed_time_oracle (hN : 0 < N) (z X : Fin N → E d)
    (m μ : E d) (Sigma A B : Mat d) (hB : IsUnit B)
    (hX : ∀ i, X i = m + matVec B (z i)) (hSigma : B * B.transpose = Sigma)
    (S b D₀ : ℝ)
    (hstable : coordinateSqDist (m, covarianceRoot Sigma) (μ, A) ≤ S ^ 2 * D₀)
    (hspectral : (covarianceMax B : ℝ) ≤ b ^ 2) :
    w2sq (empiricalLaw X) (gaussianLaw μ A) ≤
      ENNReal.ofReal (2 * S ^ 2 * D₀) +
        ENNReal.ofReal (2 * b ^ 2) * w2sq (empiricalLaw z) (standardGaussian d) := by
  letI := empiricalLaw_probability hN X
  letI := GaussianAffine.gaussianLaw_probability m (covarianceRoot Sigma)
  letI := GaussianAffine.gaussianLaw_probability μ A
  have hshape := (empirical_affine_two_sided hN z m B hB).2
  have hcloud : (fun i => m + matVec B (z i)) = X := by
    funext i
    exact (hX i).symm
  rw [hcloud, hSigma] at hshape
  have hcov : (covarianceMax B : ℝ≥0∞) ≤ ENNReal.ofReal (b ^ 2) := by
    have hh := ENNReal.ofReal_le_ofReal hspectral
    simpa only [ENNReal.ofReal_coe_nnreal] using hh
  have hshape' : w2sq (empiricalLaw X) (gaussianLaw m (covarianceRoot Sigma)) ≤
      ENNReal.ofReal (b ^ 2) * w2sq (empiricalLaw z) (standardGaussian d) :=
    hshape.trans (mul_le_mul_right' hcov _)
  have hmom : w2sq (gaussianLaw m (covarianceRoot Sigma)) (gaussianLaw μ A) ≤
      ENNReal.ofReal (S ^ 2 * D₀) := by
    exact (GaussianCoupling.gaussian_w2sq_le m μ (covarianceRoot Sigma) A).trans
      (ENNReal.ofReal_le_ofReal hstable)
  calc
    w2sq (empiricalLaw X) (gaussianLaw μ A) ≤
        2 * w2sq (empiricalLaw X) (gaussianLaw m (covarianceRoot Sigma)) +
        2 * w2sq (gaussianLaw m (covarianceRoot Sigma)) (gaussianLaw μ A) :=
      w2sq_triangle _ _ _
    _ ≤ 2 * (ENNReal.ofReal (b ^ 2) * w2sq (empiricalLaw z) (standardGaussian d)) +
        2 * ENNReal.ofReal (S ^ 2 * D₀) :=
      add_le_add (mul_le_mul_left' hshape' 2) (mul_le_mul_left' hmom 2)
    _ = _ := by
      have he1 : (2 : ℝ≥0∞) * ENNReal.ofReal (S ^ 2 * D₀) =
          ENNReal.ofReal (2 * S ^ 2 * D₀) := by
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring
      have he2 : (2 : ℝ≥0∞) * (ENNReal.ofReal (b ^ 2) *
          w2sq (empiricalLaw z) (standardGaussian d)) =
          ENNReal.ofReal (2 * b ^ 2) * w2sq (empiricalLaw z) (standardGaussian d) := by
        have hc : (2 : ℝ≥0∞) * ENNReal.ofReal (b ^ 2) = ENNReal.ofReal (2 * b ^ 2) := by
          rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
        rw [← mul_assoc, hc]
      rw [he1, he2, add_comm]

/-- Taking the time supremum loses no factor and requires no interchange of
supremum and expectation. This is the deterministic estimate in (2.10), as an
assembly component pending the source's global-flow and sublevel lemmas. -/
theorem all_time_oracle_of_affine_and_moment_stability
    (hN : 0 < N) (x : Fin N → E d) (W : Mat d)
    (X : Specification.ParticlePath d N) (p : Specification.MomentPath d)
    (B : ℝ → Mat d) (S b : ℝ)
    (hB : ∀ t, 0 ≤ t → IsUnit (B t))
    (hX : ∀ t, 0 ≤ t → ∀ i, X t i = empiricalMean (X t) +
      matVec (B t) (standardizedCloud x W i))
    (hSigma : ∀ t, 0 ≤ t → B t * (B t).transpose = empiricalCovariance (X t))
    (hstable : ∀ t, 0 ≤ t →
      coordinateSqDist (Specification.cloudQ (X t)) (p.q t) ≤
        S ^ 2 * coordinateSqDist (Specification.cloudQ x) (p.q 0))
    (hspectral : ∀ t, 0 ≤ t → (covarianceMax (B t) : ℝ) ≤ b ^ 2) :
    Specification.pathSup X p ≤
      ENNReal.ofReal (2 * S ^ 2 * coordinateSqDist (Specification.cloudQ x) (p.q 0)) +
        ENNReal.ofReal (2 * b ^ 2) *
          w2sq (empiricalLaw (standardizedCloud x W)) (standardGaussian d) := by
  apply iSup_le
  intro t
  exact fixed_time_oracle hN (standardizedCloud x W) (X t)
    (empiricalMean (X t)) (p.mean t) (empiricalCovariance (X t))
    (covarianceRoot (p.cov t)) (B t) (hB t t.property)
    (hX t t.property) (hSigma t t.property) S b
    (coordinateSqDist (Specification.cloudQ x) (p.q 0))
    (hstable t t.property) (hspectral t t.property)

/-- The oracle assembly for an actual particle solution; its affine
representation and covariance factorization are now derived from the linear
fundamental equation rather than included as input equalities. -/
theorem all_time_oracle_from_fundamental (hN : 0 < N)
    (V : E d → ℝ) (X : Specification.ParticlePath d N) (hX : particleSolution V X)
    (p : Specification.MomentPath d)
    (hC : ContinuousOn (fun t => particleCoefficient V (X t)) (Set.Ici 0))
    (L : ℝ → Mat d) (hL0 : L 0 = 1)
    (hL : ∀ t, 0 ≤ t → HasDerivWithinAt L
      (particleCoefficient V (X t) * L t) (Set.Ici 0) t)
    (hLunit : ∀ t, 0 ≤ t → IsUnit (L t))
    (W : Mat d) (hW : IsWhitening (X 0) W) (S b : ℝ)
    (hstable : ∀ t, 0 ≤ t →
      coordinateSqDist (Specification.cloudQ (X t)) (p.q t) ≤
        S ^ 2 * coordinateSqDist (Specification.cloudQ (X 0)) (p.q 0))
    (hspectral : ∀ t, 0 ≤ t → (covarianceMax (L t * W⁻¹) : ℝ) ≤ b ^ 2) :
    Specification.pathSup X p ≤
      ENNReal.ofReal (2 * S ^ 2 * coordinateSqDist (Specification.cloudQ (X 0)) (p.q 0)) +
        ENNReal.ofReal (2 * b ^ 2) *
          w2sq (empiricalLaw (standardizedCloud (X 0) W)) (standardGaussian d) := by
  have hd := (Matrix.isUnit_iff_isUnit_det W).mp
    (TransportParticleAffine.whitening_isUnit (X 0) W hW)
  have hWinv : IsUnit W⁻¹ := (Matrix.isUnit_iff_isUnit_det W⁻¹).mpr
    (Matrix.isUnit_nonsing_inv_det W hd)
  apply all_time_oracle_of_affine_and_moment_stability hN (X 0) W X p
    (fun t => L t * W⁻¹) S b
    (fun t ht => (hLunit t ht).mul hWinv) ?_ ?_ hstable hspectral
  · intro t ht i
    exact (TransportParticleAffine.particle_affine_representation hN V X hX hC L hL0 hL t ht i).trans
      ((TransportParticleAffine.standardized_affine_lift (X 0) W (L t) hW
        (empiricalMean (X t))).1 i)
  · intro t ht
    exact (TransportParticleAffine.standardized_affine_lift (X 0) W (L t) hW
      (empiricalMean (X t))).2.trans
      (TransportParticleAffine.particle_affine_covariance hN V X hX hC L hL0 hL t ht).symm

end Paper38.DeterministicOracle
