import Paper38.Rates
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The actual objects of P38

These definitions fix the original Euclidean/Gaussian/particle model. They do
not contain assumptions of any of the paper's conclusions. Norms of matrices
are explicit Frobenius sums, rather than the default matrix operator norm.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped BigOperators Matrix MatrixOrder ENNReal

namespace Paper38.Model

abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ
abbrev Coordinates (d : ℕ) := E d × Mat d

def vec (d : ℕ) (x : Fin d → ℝ) : E d := WithLp.toLp 2 x

def matVec {d : ℕ} (A : Mat d) (x : E d) : E d :=
  vec d (A.mulVec (WithLp.ofLp x))

def outer {d : ℕ} (x y : E d) : Mat d := fun i j => x i * y j

def frobSq {d : ℕ} (A : Mat d) : ℝ := ∑ i, ∑ j, A i j ^ 2

def coordinateSqDist {d : ℕ} (q r : Coordinates d) : ℝ :=
  ‖q.1 - r.1‖ ^ 2 + frobSq (q.2 - r.2)

def domain (d : ℕ) : Set (Coordinates d) := {q | q.2.PosDef}

/-- Product standard normal law in Euclidean coordinates. -/
def standardGaussian (d : ℕ) : Measure (E d) :=
  (Measure.pi (fun _ : Fin d => gaussianReal 0 1)).map (vec d)

/-- The affine image N(μ, AAᵀ); no Gaussian expectation is a free oracle. -/
def gaussianLaw {d : ℕ} (μ : E d) (A : Mat d) : Measure (E d) :=
  (standardGaussian d).map (fun z => μ + matVec A z)

def hessian {d : ℕ} (V : E d → ℝ) (x : E d) : Mat d :=
  fun i j => (fderiv ℝ (fderiv ℝ V) x (vec d (Pi.single i 1)))
    (vec d (Pi.single j 1))

/-- Exactly (2.1), with C² and globally bounded, uniformly positive Hessian. -/
structure AdmissiblePotential {d : ℕ} (V : E d → ℝ) (α β : ℝ) : Prop where
  dimension : 1 ≤ d
  alpha_pos : 0 < α
  alpha_le_beta : α ≤ β
  regularity : ContDiff ℝ 2 V
  hessian_lower : ∀ x u : E d,
    α * ‖u‖ ^ 2 ≤ (fderiv ℝ (fderiv ℝ V) x u) u
  hessian_upper : ∀ x u : E d,
    (fderiv ℝ (fderiv ℝ V) x u) u ≤ β * ‖u‖ ^ 2

/-- Principal symmetric square root, used for the covariance coordinates. -/
def covarianceRoot {d : ℕ} (S : Mat d) : Mat d := CFC.sqrt S

/-- Exact Gaussian gradient expectation m of (2.2). -/
def meanGradient {d : ℕ} (V : E d → ℝ) (μ : E d) (S : Mat d) : E d :=
  ∫ x, gradient V x ∂gaussianLaw μ (covarianceRoot S)

/-- Exact Gaussian Hessian expectation Γ of (2.2), entrywise Bochner integral. -/
def meanHessian {d : ℕ} (V : E d → ℝ) (μ : E d) (S : Mat d) : Mat d :=
  fun i j => ∫ x, hessian V x i j ∂gaussianLaw μ (covarianceRoot S)

/-- The constant-free reverse-KL energy in principal square-root coordinates. -/
def energy {d : ℕ} (V : E d → ℝ) (q : Coordinates d) : ℝ :=
  (∫ z, V (q.1 + matVec q.2 z) ∂standardGaussian d) - Real.log q.2.det

def sublevel {d : ℕ} (V : E d → ℝ) (qstar : Coordinates d) (R : ℝ) :
    Set (Coordinates d) := {q | q ∈ domain d ∧ energy V q - energy V qstar ≤ R}

/-- The moment vector field (2.3), in mean/covariance coordinates. -/
def momentField {d : ℕ} (V : E d → ℝ) (μ : E d) (S : Mat d) : E d × Mat d :=
  let m := meanGradient V μ S
  let Γ := meanHessian V μ S
  (matVec (1 - Γ * S) μ - (1 + ‖μ‖ ^ 2) • m,
    2 • S - S * (S * Γ + outer μ m) - (Γ * S + outer m μ) * S)

def momentSolution {d : ℕ} (V : E d → ℝ) (μ : ℝ → E d) (S : ℝ → Mat d) : Prop :=
  (∀ t, 0 ≤ t → (S t).PosDef) ∧
  ∀ t, 0 ≤ t → HasDerivWithinAt μ (momentField V (μ t) (S t)).1 (Set.Ici 0) t ∧
    HasDerivWithinAt S (momentField V (μ t) (S t)).2 (Set.Ici 0) t

def empiricalMean {d N : ℕ} (x : Fin N → E d) : E d :=
  (N : ℝ)⁻¹ • ∑ i, x i

def empiricalCovariance {d N : ℕ} (x : Fin N → E d) : Mat d :=
  (N : ℝ)⁻¹ • ∑ i, outer (x i - empiricalMean x) (x i - empiricalMean x)

def empiricalLaw {d N : ℕ} (x : Fin N → E d) : Measure (E d) :=
  (ENNReal.ofReal (N : ℝ)⁻¹) • ∑ i, Measure.dirac (x i)

def particleCoefficient {d N : ℕ} (V : E d → ℝ) (x : Fin N → E d) : Mat d :=
  1 - meanHessian V (empiricalMean x) (empiricalCovariance x) * empiricalCovariance x -
    outer (meanGradient V (empiricalMean x) (empiricalCovariance x)) (empiricalMean x)

def particleField {d N : ℕ} (V : E d → ℝ) (x : Fin N → E d) (i : Fin N) : E d :=
  matVec (particleCoefficient V x) (x i) -
    meanGradient V (empiricalMean x) (empiricalCovariance x)

def particleSolution {d N : ℕ} (V : E d → ℝ) (x : ℝ → Fin N → E d) : Prop :=
  (∀ t, 0 ≤ t → (empiricalCovariance (x t)).PosDef) ∧
  ∀ t, 0 ≤ t → ∀ i,
    HasDerivWithinAt (fun s => x s i) (particleField V (x t) i) (Set.Ici 0) t

/-- Whitening is a constraint on the actual empirical covariance. -/
def IsWhitening {d N : ℕ} (x : Fin N → E d) (R : Mat d) : Prop :=
  R * empiricalCovariance x * R.transpose = 1

def standardizedCloud {d N : ℕ} (x : Fin N → E d) (R : Mat d) : Fin N → E d :=
  fun i => matVec R (x i - empiricalMean x)


end Paper38.Model
