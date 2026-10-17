import Paper38.Specification
import Paper38.GaussianCoupling
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Actual raw Gaussian sampling objects shared by every external statistical
input. These definitions include no particle trajectories or convergence bound. -/
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace Paper38.Sampling
open Model

abbrev Sample (d N : ℕ) := Specification.Sample d N
abbrev law (d N : ℕ) := Specification.sampleLaw d N

def cloud (d N : ℕ) (ω : Sample d N) : Fin N → E d :=
  fun i => vec d (fun j => ω (i,j))

def covariance (d N : ℕ) (ω : Sample d N) : Mat d := empiricalCovariance (cloud d N ω)
def mean (d N : ℕ) (ω : Sample d N) : E d := empiricalMean (cloud d N ω)
def defect (d N : ℕ) (ω : Sample d N) : ℝ :=
  frobSq (1 - covariance d N ω) + ‖mean d N ω‖ ^ 2

def opNorm {d : ℕ} (A : Mat d) : ℝ :=
  ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

def good (d N : ℕ) : Set (Sample d N) :=
  {ω | ‖mean d N ω‖ ≤ 1 / 4 ∧ opNorm (covariance d N ω - 1) ≤ 1 / 4}

def standardized (d N : ℕ) (ω : Sample d N) : Fin N → E d :=
  standardizedCloud (cloud d N ω) (covarianceRoot (covariance d N ω))⁻¹

def rawLaw (d N : ℕ) (ω : Sample d N) : Measure (E d) := empiricalLaw (cloud d N ω)
def shapeLaw (d N : ℕ) (ω : Sample d N) : Measure (E d) := empiricalLaw (standardized d N ω)
def rawError (d N : ℕ) (ω : Sample d N) : ℝ≥0∞ :=
  Transport.w2sq (rawLaw d N ω) (standardGaussian d)
def shapeError (d N : ℕ) (ω : Sample d N) : ℝ≥0∞ :=
  Transport.w2sq (shapeLaw d N ω) (standardGaussian d)

def logDetDefect (d N : ℕ) (ω : Sample d N) : ℝ :=
  max (-Real.log (covariance d N ω).det) 0

lemma defect_nonneg (d N : ℕ) (ω : Sample d N) : 0 ≤ defect d N ω := by
  exact add_nonneg (Finset.sum_nonneg fun _ _ =>
    Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)

instance law_probability (d N : ℕ) : IsProbabilityMeasure (law d N) :=
  GaussianStatistics.gaussianSampleLaw_probability N d

/-- Initial quantities in (7.15), before any dynamics. -/
def initializedMeanSq (μ : E d) (S : Mat d) (N : ℕ) (ω : Sample d N) : ℝ :=
  ‖empiricalMean (Specification.gaussianCloud μ S N ω)‖ ^ 2

def initializedTrace (μ : E d) (S : Mat d) (N : ℕ) (ω : Sample d N) : ℝ :=
  (empiricalCovariance (Specification.gaussianCloud μ S N ω)).trace

def initializedLog (μ : E d) (S : Mat d) (N : ℕ) (ω : Sample d N) : ℝ :=
  max (-Real.log (empiricalCovariance (Specification.gaussianCloud μ S N ω)).det) 0

def initialEnvelope (μ : E d) (S : Mat d) (N : ℕ) (ω : Sample d N) : ℝ :=
  1 + initializedMeanSq μ S N ω + initializedTrace μ S N ω + initializedLog μ S N ω

end Paper38.Sampling
