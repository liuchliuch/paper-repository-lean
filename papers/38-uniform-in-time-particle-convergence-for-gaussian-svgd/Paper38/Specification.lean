import Paper38.Model
import Paper38.Transport
import Paper38.RandomSupremum
import Paper38.GaussianStatistics

/-!
# Source statement specification for the principal results

The propositions below are targets, NOT assumed theorems and NOT fields of a
proof certificate. They use the original Gaussian integrals, finite empirical
cloud, physical-time derivative, and infimum over actual transport couplings.
The corresponding proof status is recorded in coverage.json. In particular,
defining one of these propositions is never counted as proving it.
-/

noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
namespace Paper38.Specification
open Model

abbrev Sample (d N : ℕ) := Fin N × Fin d → ℝ

def sampleLaw (d N : ℕ) : Measure (Sample d N) :=
  GaussianStatistics.gaussianSampleLaw N d

def gaussianCloud {d : ℕ} (μ : E d) (S : Mat d) (N : ℕ)
    (ω : Sample d N) : Fin N → E d :=
  fun i => μ + matVec (covarianceRoot S) (vec d (fun j => ω (i,j)))

def IsMinimizer {d : ℕ} (V : E d → ℝ) (qstar : Coordinates d) : Prop :=
  qstar ∈ domain d ∧ ∀ q ∈ domain d, energy V qstar ≤ energy V q

def IsUniqueMinimizer {d : ℕ} (V : E d → ℝ) (qstar : Coordinates d) : Prop :=
  IsMinimizer V qstar ∧ ∀ q, IsMinimizer V q → q = qstar

structure MomentPath (d : ℕ) where
  mean : ℝ → E d
  cov : ℝ → Mat d

def MomentPath.q {d : ℕ} (p : MomentPath d) (t : ℝ) : Coordinates d :=
  (p.mean t, covarianceRoot (p.cov t))

def MomentPath.law {d : ℕ} (p : MomentPath d) (t : ℝ) : Measure (E d) :=
  gaussianLaw (p.mean t) (covarianceRoot (p.cov t))

def IsMomentPathFrom {d : ℕ} (V : E d → ℝ) (μ : E d) (S : Mat d)
    (p : MomentPath d) : Prop :=
  momentSolution V p.mean p.cov ∧ p.mean 0 = μ ∧ p.cov 0 = S

def MomentWellPosed {d : ℕ} (V : E d → ℝ) (μ : E d) (S : Mat d) : Prop :=
  ∃ p, IsMomentPathFrom V μ S p ∧
    ∀ p', IsMomentPathFrom V μ S p' → ∀ t, 0 ≤ t →
      p'.mean t = p.mean t ∧ p'.cov t = p.cov t

abbrev ParticlePath (d N : ℕ) := ℝ → Fin N → E d

def IsParticlePathFrom {d N : ℕ} (V : E d → ℝ) (x : Fin N → E d)
    (X : ParticlePath d N) : Prop := particleSolution V X ∧ X 0 = x

def ParticleWellPosed {d N : ℕ} (V : E d → ℝ) (x : Fin N → E d) : Prop :=
  ∃ X, IsParticlePathFrom V x X ∧
    ∀ X', IsParticlePathFrom V x X' → ∀ t, 0 ≤ t → X' t = X t

def pathError {d N : ℕ} (X : ParticlePath d N) (p : MomentPath d) (t : ℝ) : ℝ≥0∞ :=
  Transport.w2sq (empiricalLaw (X t)) (p.law t)

def pathSup {d N : ℕ} (X : ParticlePath d N) (p : MomentPath d) : ℝ≥0∞ :=
  RandomSupremum.timeSup (pathError X p)

def cloudQ {d N : ℕ} (x : Fin N → E d) : Coordinates d :=
  (empiricalMean x, covarianceRoot (empiricalCovariance x))

/-- Full source oracle (2.10), including global well-posedness. Quantification
of its constants precedes arbitrary deterministic cloud and initial moments. -/
def Theorem21 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ qstar, IsUniqueMinimizer V qstar → ∀ R : ℝ, 0 ≤ R →
  ∃ S b : ℝ, 0 ≤ S ∧ 0 < b ∧
  ∀ (N : ℕ) (μ0 : E d) (S0 : Mat d) (x : Fin N → E d),
    0 < N → S0.PosDef → (empiricalCovariance x).PosDef →
    (μ0, covarianceRoot S0) ∈ sublevel V qstar R →
    cloudQ x ∈ sublevel V qstar R →
    MomentWellPosed V μ0 S0 ∧ ParticleWellPosed V x ∧
    ∀ (p : MomentPath d) (X : ParticlePath d N), IsMomentPathFrom V μ0 S0 p →
      IsParticlePathFrom V x X → ∀ W : Mat d, IsWhitening x W →
      pathSup X p ≤ ENNReal.ofReal (2 * S ^ 2 * coordinateSqDist (cloudQ x) (p.q 0)) +
        ENNReal.ofReal (2 * b ^ 2) *
          Transport.w2sq (empiricalLaw (standardizedCloud x W)) (standardGaussian d)

/-- Full source expectation theorem (2.12) on the canonical i.i.d. Gaussian
sample space. The same C is required for every N≥d+1. -/
def Theorem22 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ (μ0 : E d) (S0 : Mat d), S0.PosDef →
  ∃ (p : MomentPath d) (C : ℝ), 0 < C ∧ IsMomentPathFrom V μ0 S0 p ∧
  ∀ N : ℕ, d + 1 ≤ N →
    (∀ᵐ ω ∂sampleLaw d N, (empiricalCovariance (gaussianCloud μ0 S0 N ω)).PosDef) ∧
    ∃ X : Sample d N → ParticlePath d N,
      (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) ∧
      Measurable (fun ω => pathSup (X ω) p) ∧
      (∫⁻ ω, pathSup (X ω) p ∂sampleLaw d N) ≤ ENNReal.ofReal (C * rate d N)

/-- Sharpness (2.13), stated for the same global particle dynamics and the
actual Gaussian initialization, rather than an arbitrary error sequence. -/
def Proposition23 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ (μ0 : E d) (S0 : Mat d), S0.PosDef →
  ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ), d + 1 ≤ N →
  ∀ (p : MomentPath d) (X : Sample d N → ParticlePath d N),
    IsMomentPathFrom V μ0 S0 p →
    (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
    ENNReal.ofReal (c * rate d N) ≤ ∫⁻ ω, pathSup (X ω) p ∂sampleLaw d N

/-- High-probability all-time and last-iterate conclusions (2.14)-(2.15).
The constants are chosen before N and the tail parameter x. -/
def Theorem24 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ qstar, IsUniqueMinimizer V qstar →
  ∀ (μ0 : E d) (S0 : Mat d), S0.PosDef →
  ∃ C c c0 : ℝ, 0 < C ∧ 0 < c ∧ 0 < c0 ∧
  ∀ (N : ℕ), d + 1 ≤ N →
  ∀ (p : MomentPath d) (X : Sample d N → ParticlePath d N),
    IsMomentPathFrom V μ0 S0 p →
    (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
  ∀ x : ℝ, 1 ≤ x → x ≤ c0 * N → ∃ H : Set (Sample d N), MeasurableSet H ∧
    sampleLaw d N Hᶜ ≤ ENNReal.ofReal (C * Real.exp (-c * x)) ∧
    ∀ ω ∈ H, pathSup (X ω) p ≤ ENNReal.ofReal (C * (rate d N + x / N)) ∧
      ∀ t : ℝ, 0 ≤ t →
        Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2) ≤
          ENNReal.ofReal (C * (rate d N + x / N + Real.exp (-2 * c * t)))

/-- Physical-time last-iterate estimate (2.16), with constants uniform in N,t. -/
def Corollary25 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ qstar, IsUniqueMinimizer V qstar →
  ∀ (μ0 : E d) (S0 : Mat d), S0.PosDef →
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ N : ℕ, d + 1 ≤ N →
  ∀ X : Sample d N → ParticlePath d N,
    (∀ᵐ ω ∂sampleLaw d N, IsParticlePathFrom V (gaussianCloud μ0 S0 N ω) (X ω)) →
  ∀ t : ℝ, 0 ≤ t →
    (∫⁻ ω, Transport.w2sq (empiricalLaw (X ω t)) (gaussianLaw qstar.1 qstar.2)
      ∂sampleLaw d N) ≤ ENNReal.ofReal (C * (rate d N + Real.exp (-2 * c * t)))

/-- Existence/uniqueness, strong convexity and coercivity are not fields in
AdmissiblePotential: the unique minimizer is itself a proof obligation. -/
def Lemma42_minimizer : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
    ∃ qstar : Coordinates d, IsUniqueMinimizer V qstar

/-- Lemma 5.1 in principal square-root covariance coordinates. -/
def Lemma51 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ qstar, IsUniqueMinimizer V qstar → ∀ R : ℝ, 0 ≤ R →
    ∃ S : ℝ, 0 ≤ S ∧ ∀ (p p' : MomentPath d),
      momentSolution V p.mean p.cov → momentSolution V p'.mean p'.cov →
      p.q 0 ∈ sublevel V qstar R → p'.q 0 ∈ sublevel V qstar R →
      ∀ t : ℝ, 0 ≤ t → coordinateSqDist (p.q t) (p'.q t) ≤
        S ^ 2 * coordinateSqDist (p.q 0) (p'.q 0)

end Paper38.Specification
