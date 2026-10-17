import Paper38.GaussianLocalization
import Paper38.ExternalStatisticalInputs

/-!
# Source Proposition 2.3: sharpness in particle number

The lower bound comes from the physical time zero, the actual invertible
Gaussian initialization map, and the raw empirical Gaussian matching lower
bound. No statement about a particle error is supplied as an input.
-/
noncomputable section
open MeasureTheory
open scoped NNReal ENNReal
namespace Paper38.SourceSharpness
open Model Specification Sampling AffineLifting ExternalStatisticalInputs

variable {d : ℕ} [NeZero d]

/-- The actual time-zero error dominates the raw standard Gaussian sample
error by the smallest squared singular value of the initialization root. -/
theorem initial_error_lower {N : ℕ} (hN : 0 < N) (μ0 : E d) (S0 : Mat d)
    (hS0 : S0.PosDef) (ω : Specification.Sample d N) :
    (covarianceMin (covarianceRoot S0) : ℝ≥0∞) * rawError d N ω ≤
      Transport.w2sq (empiricalLaw (gaussianCloud μ0 S0 N ω))
        (gaussianLaw μ0 (covarianceRoot S0)) := by
  letI := empiricalLaw_probability hN (cloud d N ω)
  letI := GaussianAffine.standardGaussian_probability d
  have h := (matrix_affine_two_sided (empiricalLaw (cloud d N ω))
    (standardGaussian d) μ0 (covarianceRoot S0) hS0.posDef_sqrt.isUnit).1
  rw [empiricalLaw_map hN (cloud d N ω) _
    (continuous_const.add (GaussianAffine.continuous_matVec _)).measurable] at h
  exact h

/-- No regularity or measurability assumption on the supplied trajectory is
needed for this lower bound: its actual initial condition suffices. -/
theorem raw_error_le_pathSup {N : ℕ} (hN : 0 < N) (V : E d → ℝ)
    (μ0 : E d) (S0 : Mat d) (hS0 : S0.PosDef) (ω : Specification.Sample d N)
    (p : MomentPath d) (X : ParticlePath d N)
    (hp : IsMomentPathFrom V μ0 S0 p)
    (hX : IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) X) :
    (covarianceMin (covarianceRoot S0) : ℝ≥0∞) * rawError d N ω ≤ pathSup X p := by
  have h0 : Transport.w2sq (empiricalLaw (gaussianCloud μ0 S0 N ω))
      (gaussianLaw μ0 (covarianceRoot S0)) = pathError X p 0 := by
    change _ = Transport.w2sq (empiricalLaw (X 0))
      (gaussianLaw (p.mean 0) (covarianceRoot (p.cov 0)))
    rw [hX.2, hp.2.1, hp.2.2]
  exact (initial_error_lower hN μ0 S0 hS0 ω).trans
    (h0 ▸ le_iSup (fun t : {t : ℝ // 0 ≤ t} => pathError X p t) ⟨0, le_rfl⟩)

/-- Fixed d, initial mean and covariance: one strictly positive constant works
for every sample size, and for every almost-everywhere actual particle path. -/
theorem sharpness (matching : Matching d) (V : E d → ℝ) (μ0 : E d)
    (S0 : Mat d) (hS0 : S0.PosDef) :
    ∃ c : ℝ, 0 < c ∧ ∀ N : ℕ, d + 1 ≤ N →
      ∀ (p : MomentPath d) (X : Specification.Sample d N → ParticlePath d N),
      IsMomentPathFrom V μ0 S0 p →
      (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
      ENNReal.ofReal (c * rate d N) ≤ ∫⁻ ω, pathSup (X ω) p ∂sampleLaw d N := by
  let a : ℝ≥0 := covarianceMin (covarianceRoot S0)
  have ha : 0 < (a : ℝ) := GaussianLocalization.covarianceMin_pos _ hS0.posDef_sqrt
  refine ⟨(a : ℝ) * matching.lowerConstant, mul_pos ha matching.lower_pos, ?_⟩
  intro N hN p X hp hX
  have hNp : 0 < N := lt_of_lt_of_le (Nat.succ_pos d) hN
  calc
    ENNReal.ofReal (((a : ℝ) * matching.lowerConstant) * rate d N) =
        (a : ℝ≥0∞) * ENNReal.ofReal (matching.lowerConstant * rate d N) := by
      rw [mul_assoc, ENNReal.ofReal_mul ha.le, ENNReal.ofReal_coe_nnreal]
    _ ≤ (a : ℝ≥0∞) * ∫⁻ ω, rawError d N ω ∂law d N :=
      mul_le_mul_left' (matching.expected_lower N hN) _
    _ ≤ ∫⁻ ω, (a : ℝ≥0∞) * rawError d N ω ∂law d N :=
      lintegral_const_mul_le _ _
    _ ≤ ∫⁻ ω, pathSup (X ω) p ∂sampleLaw d N := by
      apply lintegral_mono_ae
      filter_upwards [hX] with ω hω
      exact raw_error_le_pathSup hNp V μ0 S0 hS0 ω p (X ω) hp hω

/-- The exact source specification, with only the explicitly authorized raw
Gaussian matching theorem supplied externally. Only its lower bound is used. -/
theorem proposition23 (matching : ∀ d : ℕ, 1 ≤ d → Matching d) :
    Specification.Proposition23 := by
  intro d V α β hV μ0 S0 hS0
  have hd := hV.dimension
  letI : NeZero d := ⟨by omega⟩
  exact sharpness (matching d hV.dimension) V μ0 S0 hS0

end Paper38.SourceSharpness
