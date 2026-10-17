import Paper38.HilbertGradientFlow
import Paper38.GaussianEnergyFacts
import Paper38.Specification

/-! Literal analytic targets for source Lemmas 4.1--4.2 and Proposition 4.3.
These are propositions to prove, never assumptions or proof-certificate inputs.
The intrinsic tangent uses the ordinary Euclidean--Frobenius inner product.
Quadratic-form bounds below are precisely the Loewner inequalities a I ≤ A ≤ b I. -/
noncomputable section
open scoped Matrix MatrixOrder Matrix.Norms.Frobenius InnerProductSpace
namespace Paper38.GeometrySpecification
open Model HilbertCoordinates Set

/-- Actual covariance-coordinate energy E(μ,Σ)=F(μ,sqrt Σ). -/
def covarianceEnergy {d : ℕ} (V : E d → ℝ) (q : Tangent d) : ℝ :=
  HilbertCoordinates.energy V (ExternalMatrixAnalysis.principalRoot q)

/-- Actual source matrix operator (4.3), with its state in covariance coordinates. -/
def covarianceMobility {d : ℕ} (q : Tangent d) : Tangent d →L[ℝ] Tangent d :=
  (HilbertMobility.encode d).comp
    ((HilbertMobility.rawM (meanProjection d q) (matrixProjection d q)).comp (toModel d))

/-- The complete energy-gradient, positive mobility and moment-field assertions
of source Lemma 4.1, including its polarized sum-of-squares formula (4.6). -/
def Lemma41 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ q ∈ Domain d,
    toModel d (gradient (covarianceEnergy V) q) =
      (meanGradient V (meanProjection d q) (matrixProjection d q),
        Mobility.energyCovGradient (matrixProjection d q)
          (meanHessian V (meanProjection d q) (matrixProjection d q))) ∧
    (∀ u v : Tangent d,
      ⟪u,covarianceMobility q v⟫_ℝ = ⟪v,covarianceMobility q u⟫_ℝ) ∧
    (∀ v : Tangent d, v ≠ 0 → 0 < ⟪v,covarianceMobility q v⟫_ℝ) ∧
    (∀ u v : Tangent d,
      ⟪u,covarianceMobility q v⟫_ℝ =
        Mobility.frobenius
          (Mobility.feature (WithLp.ofLp (meanProjection d q)) (matrixProjection d q)
            (WithLp.ofLp (meanProjection d u)) (matrixProjection d u))
          (Mobility.feature (WithLp.ofLp (meanProjection d q)) (matrixProjection d q)
            (WithLp.ofLp (meanProjection d v)) (matrixProjection d v)) +
          ⟪meanProjection d u,meanProjection d v⟫_ℝ) ∧
    toModel d (-(covarianceMobility q) (gradient (covarianceEnergy V) q)) =
      momentField V (meanProjection d q) (matrixProjection d q)

/-- C², the exact second variation (4.7), strong convexity, compact sublevels
and the literal unique Gaussian minimizer, with all original quantifiers. -/
def Lemma42 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
    ContDiffOn ℝ 2 (HilbertCoordinates.energy V) (Domain d) ∧
    (∀ q ∈ Domain d, ∀ v : Tangent d,
      fderiv ℝ (fderiv ℝ (HilbertCoordinates.energy V)) q v v =
        (∫ z, GaussianEnergy.quadraticVariation V
          (meanProjection d q) (meanProjection d v)
          (matrixProjection d q) (matrixProjection d v) z ∂standardGaussian d) +
        Matrix.trace ((matrixProjection d q)⁻¹ * matrixProjection d v *
          (matrixProjection d q)⁻¹ * matrixProjection d v)) ∧
    (∀ q ∈ Domain d, ∀ v : Tangent d,
      α * ‖v‖^2 ≤ fderiv ℝ (fderiv ℝ (HilbertCoordinates.energy V)) q v v) ∧
    EnergyDecay.StrongConvexGradientOn (HilbertCoordinates.energy V)
      (gradient (HilbertCoordinates.energy V)) (Domain d) α ∧
    (∀ c : ℝ, IsCompact {q : Tangent d | q ∈ Domain d ∧ HilbertCoordinates.energy V q ≤ c}) ∧
    ∃ qstar : Coordinates d, Specification.IsUniqueMinimizer V qstar

def sublevel {d : ℕ} (V : E d → ℝ) (z : Tangent d) (R : ℝ) : Set (Tangent d) :=
  {q | q ∈ Domain d ∧ HilbertCoordinates.energy V q-HilbertCoordinates.energy V z ≤ R}

/-- Source (4.11), in its equivalent ordinary quadratic-form formulation,
plus the singular bounds used to prove the explicit constant (4.12). -/
def SpectralBounds {d : ℕ} (q : Tangent d) (M a b : ℝ) : Prop :=
  ‖meanProjection d q‖ ≤ M ∧
    (∀ v : E d, a * ‖v‖^2 ≤ ⟪v,matVec (matrixProjection d q) v⟫_ℝ ∧
      ⟪v,matVec (matrixProjection d q) v⟫_ℝ ≤ b * ‖v‖^2) ∧
    (∀ v : E d, a^2 * ‖v‖^2 ≤ ‖matVec (matrixProjection d q) v‖^2 ∧
      ‖matVec (matrixProjection d q) v‖^2 ≤ b^2 * ‖v‖^2)

def IsGradientPath {d : ℕ} (V : E d → ℝ) (q : ℝ → Tangent d) : Prop :=
  (∀ t, 0 ≤ t → q t ∈ Domain d) ∧
    ∀ t, 0 ≤ t → HasDerivWithinAt q (HilbertGradientFlow.field V (q t)) (Ici 0) t

/-- Full sublevel geometry, the actual explicit p_R, global flow, all-trajectory
trapping and (4.13)--(4.14). The formulas hold also at R=0, when every trajectory
is proved stationary. The final component gives the identical physical-time
moment conclusions for the source system (2.3). -/
def Proposition43 : Prop :=
  ∀ (d : ℕ) (V : E d → ℝ) (α β : ℝ), AdmissiblePotential V α β →
  ∀ z ∈ Domain d, (∀ x ∈ Domain d, HilbertCoordinates.energy V z ≤ HilbertCoordinates.energy V x) →
  ∀ R : ℝ, 0 ≤ R → ∃ M a b : ℝ, 0 < M ∧ 0 < a ∧ 0 < b ∧
    (∀ q ∈ sublevel V z R, SpectralBounds q M a b) ∧
    (∀ q ∈ sublevel V z R, a • (1 : Mat d) ≤ matrixProjection d q ∧
      matrixProjection d q ≤ b • (1 : Mat d)) ∧
    0 < MobilityEllipticity.sublevelConstant a M b ∧
    (∀ q ∈ sublevel V z R, ∀ v : Tangent d,
      MobilityEllipticity.sublevelConstant a M b * ‖v‖^2 ≤ ⟪v,HilbertMobility.P q v⟫_ℝ) ∧
    (∀ x ∈ sublevel V z R, ∃ q : ℝ → Tangent d, q 0 = x ∧ IsGradientPath V q) ∧
    (∀ x ∈ sublevel V z R, ∀ s : GlobalODE.ForwardMaximalSolution (Domain d)
      (HilbertGradientFlow.field V) x, s.lifetime = ⊤) ∧
    (∀ q : ℝ → Tangent d, IsGradientPath V q → q 0 ∈ sublevel V z R →
      ∀ t, 0 ≤ t → q t ∈ sublevel V z R ∧
        HilbertCoordinates.energy V (q t)-HilbertCoordinates.energy V z ≤
          (HilbertCoordinates.energy V (q 0)-HilbertCoordinates.energy V z) *
            Real.exp (-2*α*MobilityEllipticity.sublevelConstant a M b*t) ∧
        ‖q t-z‖ ≤ Real.sqrt (2*R/α) *
          Real.exp (-α*MobilityEllipticity.sublevelConstant a M b*t) ∧
        (R = 0 → q t = z)) ∧
    (∀ μ : E d, ∀ C : Mat d, C.PosDef → Specification.MomentWellPosed V μ C) ∧
    (∀ p : Specification.MomentPath d, momentSolution V p.mean p.cov →
      p.q 0 ∈ Model.sublevel V (toModel d z) R → ∀ t, 0 ≤ t →
        p.q t ∈ Model.sublevel V (toModel d z) R ∧
        Model.energy V (p.q t)-Model.energy V (toModel d z) ≤
          (Model.energy V (p.q 0)-Model.energy V (toModel d z)) *
            Real.exp (-2*α*MobilityEllipticity.sublevelConstant a M b*t) ∧
        coordinateSqDist (p.q t) (toModel d z) ≤
          (2*R/α) * Real.exp (-2*α*MobilityEllipticity.sublevelConstant a M b*t) ∧
        (R = 0 → p.q t = toModel d z))

end Paper38.GeometrySpecification
