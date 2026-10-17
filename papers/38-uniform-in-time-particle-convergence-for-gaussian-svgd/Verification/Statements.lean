import Paper38.MomentClosure
import Paper38.Standardization
import Paper38.GaussianStatistics
import Paper38.GaussianFullRank
import Paper38.Transport
import Paper38.RandomSupremum
import Paper38.Rates
import Paper38.ScalarCounterexample
import Paper38.CosineExample
import Paper38.ModelBridges
import Paper38.GaussianCoupling
import Paper38.TransportGluing

/-!
Independent, explicit contracts for the retained components. Source-facing
contracts are specified separately in Paper38.Specification and the source
modules, with their named external theorem arguments. Definitions here are
propositions only; no contract is assumed as a field of an input certificate.
Final whole-project compilation and official comparison remain deferred.
-/
noncomputable section
open MeasureTheory Matrix
open scoped BigOperators ENNReal NNReal MatrixOrder
namespace Paper38.Contracts

abbrev Vec (d : ℕ) := Fin d → ℝ
abbrev Mat (d : ℕ) := Matrix (Fin d) (Fin d) ℝ

def MobilityBilinear : Prop :=
  ∀ (d : ℕ) (μ a a' : Vec d) (S B B' : Mat d), Sᵀ = S → Bᵀ = B → B'ᵀ = B' →
    Mobility.pairing a B (Mobility.mobilityMean μ S a' B') (Mobility.mobilityCov μ S a' B') =
      Mobility.frobenius (Mobility.feature μ S a B) (Mobility.feature μ S a' B') + a ⬝ᵥ a'

def MobilityStrict : Prop :=
  ∀ (d : ℕ) (μ a : Vec d) (S B : Mat d), S.PosDef → Bᵀ = B →
    (Mobility.pairing a B (Mobility.mobilityMean μ S a B) (Mobility.mobilityCov μ S a B) = 0 ↔
      a = 0 ∧ B = 0)

def CovarianceRank : Prop :=
  ∀ (N d : ℕ) (x : Fin N → Vec d), (Empirical.covariance x).rank ≤ N - 1

def CovarianceSpan : Prop :=
  ∀ (N d : ℕ), 0 < N → ∀ x : Fin N → Vec d,
    (Empirical.covariance x).PosDef ↔ affineSpan ℝ (Set.range x) = ⊤

def EndpointNecessary : Prop :=
  ∀ (N d : ℕ), 0 < N → ∀ x : Fin N → Vec d,
    (Empirical.covariance x).PosDef → d + 1 ≤ N

def DensityAffineSpan : Prop :=
  ∀ (d N : ℕ) (μ : Measure (EuclideanSpace ℝ (Fin d))),
    IsProbabilityMeasure μ → μ ≪ volume → d + 1 ≤ N →
    ∀ᵐ x : Fin N → EuclideanSpace ℝ (Fin d) ∂Measure.pi (fun _ => μ),
      affineSpan ℝ (Set.range x) = ⊤

def ParticleMomentClosure : Prop :=
  ∀ (N d : ℕ), 0 < N → ∀ (X : ℝ → Fin N → Vec d) (t : ℝ) (m : Vec d) (Γ : Mat d),
  Γᵀ = Γ →
  (∀ i, HasDerivAt (fun s => X s i)
    (MomentClosure.projectedCoefficient (Empirical.mean (X t)) m (Empirical.covariance (X t)) Γ
      *ᵥ X t i - m) t) →
  HasDerivAt (fun s => Empirical.mean (X s))
    (Mobility.momentMean (Empirical.mean (X t)) m (Empirical.covariance (X t)) Γ) t ∧
  HasDerivAt (fun s => Empirical.covariance (X s))
    (Mobility.momentCov (Empirical.mean (X t)) m (Empirical.covariance (X t)) Γ) t

def StandardizedResidual : Prop :=
  ∀ (N d : ℕ), 0 < N → ∀ x : Fin N → Vec d, (Empirical.covariance x).PosDef →
    let H := CFC.sqrt (Empirical.covariance x)
    ((N : ℝ)⁻¹ * ∑ i, Standardization.sqNorm (Standardization.standardized x H i - x i) =
      Standardization.frobSq (1 - H) + Standardization.sqNorm (Empirical.mean x)) ∧
    ((N : ℝ)⁻¹ * ∑ i, Standardization.sqNorm (Standardization.standardized x H i - x i) ≤
      Standardization.frobSq (1 - Empirical.covariance x) +
        Standardization.sqNorm (Empirical.mean x))

def GaussianMeanSecondMoment : Prop :=
  ∀ (N d : ℕ), N ≠ 0 →
    (∫ ω, ‖GaussianStatistics.sampleMean (N := N) (d := d) ω‖ ^ 2
      ∂GaussianStatistics.gaussianSampleLaw N d) = (d : ℝ) / N

def AffineTransport : Prop :=
  ∀ (d : ℕ) (μ ν : Measure (EuclideanSpace ℝ (Fin d))),
    IsProbabilityMeasure μ → IsProbabilityMeasure ν →
  ∀ (m : EuclideanSpace ℝ (Fin d))
    (B : EuclideanSpace ℝ (Fin d) ≃L[ℝ] EuclideanSpace ℝ (Fin d)) (a b : ℝ≥0),
    (∀ u, a * ‖u‖₊ ^ 2 ≤ ‖B u‖₊ ^ 2) → (∀ u, ‖B u‖₊ ^ 2 ≤ b * ‖u‖₊ ^ 2) →
    (a : ℝ≥0∞) * Transport.w2sq μ ν ≤
      Transport.w2sq (μ.map (Transport.affineEquiv m B)) (ν.map (Transport.affineEquiv m B)) ∧
    Transport.w2sq (μ.map (Transport.affineEquiv m B)) (ν.map (Transport.affineEquiv m B)) ≤
      (b : ℝ≥0∞) * Transport.w2sq μ ν

def FiniteShapeFloor : Prop :=
  ∀ (N d : ℕ) (x : Fin N → EuclideanSpace ℝ (Fin d))
    (ν : Measure (EuclideanSpace ℝ (Fin d))), IsProbabilityMeasure ν → NoAtoms ν →
    0 < Transport.w2sq (Transport.empirical x) ν

def PhysicalTimeCountability : Prop :=
  ∀ f : ℝ → ℝ≥0∞, ContinuousOn f (Set.Ici 0) →
    RandomSupremum.timeSup f = RandomSupremum.rationalSup f

def RateDominatesMean : Prop :=
  ∀ d N : ℕ, 1 ≤ d → 1 ≤ N → (N : ℝ)⁻¹ ≤ Model.rate d N

/-- Proposition 8.1: the full existential source assertion, including genuine
Gaussian integral coefficients, the initial-value problem and all time/initial
value quantifiers. A quadratic witness is permitted by the source assertion. -/
def ScalarCounterexample : Prop :=
  ∃ (V : ℝ → ℝ) (φ : ℝ → ℝ → ℝ), ContDiff ℝ ⊤ V ∧
    StrongConvexOn (Set.univ : Set ℝ) 1 V ∧
    (∀ x, 1 ≤ deriv (deriv V) x ∧ deriv (deriv V) x ≤ 1) ∧
    (∀ r, 0 < r → φ 0 r = r) ∧
    (∀ t r, 0 ≤ t → 0 < r → 0 < φ t r) ∧
    (∀ t r, 0 ≤ t → HasDerivAt (fun s : ℝ => ((0 : ℝ), (φ s r) ^ 2))
      (Paper38.ScalarCounterexample.gaussianMomentField V 0 ((φ t r) ^ 2)) t) ∧
    (¬ ∃ S : ℝ, ∀ t : ℝ, 0 ≤ t → ∀ r q : ℝ, 0 < r → 0 < q →
      |φ t r - φ t q| ≤ S * |r - q|)

def CosineHessian : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 → ∀ x : ℝ,
    1 - ε ≤ deriv (deriv (Cosine.potential ε)) x ∧
      deriv (deriv (Cosine.potential ε)) x ≤ 1 + ε

def CosineOptimum : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 10 →
    ∃ r : ℝ, 0 < r ∧ r * (1 - ε * Real.exp (-r / 2)) = 1 ∧
      (∀ μ s : ℝ, 0 < s → Cosine.energy ε 0 r ≤ Cosine.energy ε μ s) ∧
      (∀ μ s : ℝ, 0 < s → Cosine.energy ε μ s = Cosine.energy ε 0 r →
        μ = 0 ∧ s = r)

/-- Actual source Euclidean covariance, including any density and all N≥d+1. -/
def DensityPositiveCovariance : Prop :=
  ∀ (d N : ℕ) (μ : Measure (Model.E d)), IsProbabilityMeasure μ →
    μ ≪ volume → d + 1 ≤ N →
    ∀ᵐ x : Fin N → Model.E d ∂Measure.pi (fun _ => μ),
      (Model.empiricalCovariance x).PosDef

/-- Exact synchronous Gaussian comparison (5.9). -/
def GaussianSynchronous : Prop :=
  ∀ (d : ℕ) (μ ν : Model.E d) (A B : Model.Mat d),
    Transport.w2sq (Model.gaussianLaw μ A) (Model.gaussianLaw ν B) ≤
      ENNReal.ofReal (‖μ - ν‖ ^ 2 + Model.frobSq (A - B))

/-- The real coupling-based squared triangle used by the oracle. -/
def QuadraticTriangle : Prop :=
  ∀ (d : ℕ) (μ ν ξ : Measure (Model.E d)), IsProbabilityMeasure μ →
    IsProbabilityMeasure ν → IsProbabilityMeasure ξ →
      Transport.w2sq μ ξ ≤ 2 * Transport.w2sq μ ν + 2 * Transport.w2sq ν ξ

end Paper38.Contracts
