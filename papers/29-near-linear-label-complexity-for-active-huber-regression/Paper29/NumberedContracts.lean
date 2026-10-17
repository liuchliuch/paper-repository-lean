import Paper29.ExpandedSpecification
import Paper29.Minimax
import Paper29.PilotSampling
import Paper29.GeneralTranscriptDefs
import Paper29.ExternalConvexSelection

/-! Complete numbered contracts are stated as propositions from the original
objects. They contain no required Huber conclusion as an external premise.
The known generic mathematical inputs remain named and explicit. This module
imports no CheckedExpanded, LowerProof, MinimaxProof or general transcript
solution. The pilot module is needed for the dependent observed-label selector
and positive-probability definitions used in the literal pilot statement. -/
noncomputable section
set_option linter.unusedVariables false
open scoped BigOperators Classical ENNReal
open MeasureTheory Filter
namespace Paper29.ExpandedSpecification
open WeightConstruction Chaining ProcessTools ExternalCovering GeneralInformation GeneralTranscript Attainment ExternalConvexSelection

def theorem22 : Prop := QueryModel.LowerBoundStatement

def corollary23 : Prop :=
  ∀ C Cₜ Cₑ : ℝ,0<C → 0<Cₜ → 0<Cₑ →
    ExternalProcess.AnchoredChaining C → RadiusLogNonexpansive →
    HuberPrimitive 4 Cₜ → PowerPrimitive Cₑ → LewisOneNormalization → QueryModel.MinimaxBoundsStatement

def lemma32Construction : Prop :=
  ∀ {n d : ℕ} [Nonempty (Fin n)] (A : Matrix (Fin n) (Fin d) ℝ),
    A.rank=d → (∀ i,A i≠0) → RadiusLogNonexpansive → ∀ j₀ : ℤ,
    ∃ w : ℕ → PositiveWeights n,
      (∀ (k : ℕ) (i : Fin n),(2:ℝ)^(j₀+(k:ℤ))/4 ≤ huber (Leverage.radius A (w k) i)/Leverage.leverage A (w k) i ∧
        huber (Leverage.radius A (w k) i)/Leverage.leverage A (w k) i ≤ 4*(2:ℝ)^(j₀+(k:ℤ))) ∧
      (∀ k i,w (k+1) i ≤ 2*w k i) ∧ (∀ k,(∑ i,Leverage.leverage A (w k) i)=(d:ℝ))

def lemma32 : Prop :=
  lemma32Construction ∧
    ∀ (α C : ℝ),1≤α → 0≤C → HuberPrimitive α C →
    ∀ {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ),A.rank=d → (∀ i,A i≠0) →
    ∀ (a b : ℤ),a≤b → 4*Real.log (2*(n:ℝ)) ≤ ((Finset.Icc a b).card:ℝ) →
    ∀ scheme : HuberScheme A a b α,
      (∀ j,(∑ i,Leverage.leverage A (scheme.w j) i)=(d:ℝ)) ∧
      gamma2 (T:=Ball A ((2:ℝ)^(b+1)))
        (fun h k => huberMetric A (maxScore A (Finset.Icc a b) scheme.w) h k) ≤
        ENNReal.ofReal (C*Real.sqrt ((2:ℝ)^(b+1))*ProcessTools.logFactor n)

def lemma33 : Prop :=
  ∀ {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 1 ≤ n) (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)
    (w : PositiveWeights n) (p : ℕ) (hp : p = 1 ∨ p = 2)
    (hbase : ∀ i, (Leverage.radius A w i)^(p:ℝ) / Leverage.leverage A w i = 1)
    (C : ℝ) (hC : 0 ≤ C) (external : PowerPrimitive C),
    (∑ i, Leverage.leverage A w i) = (d:ℝ) ∧
      EndpointCover A p (Leverage.leverage A w) (2*C*ProcessTools.logFactor n)

def lemma35 : Prop :=
  ∀ {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (τ π : Fin n → ℝ) (T C G : ℝ) (hT : 0 < T) (hC : 0 ≤ C) (hG : 0 ≤ G)
    (external : ExternalProcess.AnchoredChaining C)
    (hτ : ∀ i, 0 < τ i) (hπ : ∀ i, 0 < π i) (hsum : ∑ i, π i = 1)
    (hm : 0 < m) (hrel : ∀ i, τ i = T * π i) (cover : ScoreGeometry A τ G)
    (ha : alpha C G T m ≤ 1) {R : ℝ} (hR : 0 < R),
    Sampling.expectation π (unshiftedError (m := m) A π R) ≤ 2 * alpha C G T m * R ∧
      Sampling.expectation π (unshiftedEnvelope (m := m) A π R) ≤ 3 * R

def lemma36 : Prop :=
  ∀ {n d m : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (hn : 1 ≤ n) (τ : Fin n → ℝ)
    (hτ : ∀ i, 0 < τ i) (C G B η δ : ℝ) (hC : 0 < C) (hG : 0 < G)
    (external : ExternalProcess.AnchoredChaining C)
    (cover : ScoreGeometry A τ (G * ProcessTools.logFactor n))
    (hB : 1 ≤ B) (hη : 0 < η) (hηhi : η < 1/2) (hδ : 0 < δ) (hδhi : δ < 1/2)
    (z : Fin n → ℝ) (hR : 0 < baseline z)
    (hsize : transferConstant C G B * (∑ i, τ i) * Real.log (2 * (n : ℝ)) ^ 3 /
      (η ^ 2 * δ ^ 2) ≤ (m : ℝ)),
    transferConstant C G B ≤ 8 * (2*C*G)^2 * B^2 ∧
    1 - δ ≤ Sampling.eventMass (Sampling.iidMass (scoreProbability τ))
      (Finset.univ.filter (fun ν : Fin m → Fin n =>
        CenteredTransferEvent A z (scoreProbability τ) (B * baseline z) (η * baseline z) ν))

def lemma39 : Prop :=
  ∀ {n d m : ℕ} (A : Matrix (Fin n) (Fin d) ℝ)
    (hn : 16 < n) (τ : Fin n → ℝ) (hτ : ∀ i, 0 < τ i)
    (C G δ : ℝ) (hC : 0 < C) (hG : 0 < G) (hδ : 0 < δ) (hδhi : δ ≤ 1)
    (external : ExternalProcess.AnchoredChaining C)
    (cover : ScoreGeometry A τ (G * ProcessTools.logFactor n))
    (hsize : (128*C*G)^2 * (2 * ∑ i, τ i) * Real.log (2*(n:ℝ))^3 *
      ((pilotGrid n).card : ℝ)^2 / δ^2 ≤ (m : ℝ))
    (b : Fin n → ℝ) (xstar : Fin d → ℝ),
    (1 - δ ≤ Sampling.eventMass (Sampling.iidMass (scoreProbability (pilotScores τ)))
      (Finset.univ.filter (fun ν : Fin m → Fin n => ∀ h,
        |Sampling.sampledUnshifted (scoreProbability (pilotScores τ)) ν A h-unshifted A h| ≤
          (1/8)*unshifted A h))) ∧
    1 - 2*δ ≤ Sampling.eventMass (Sampling.iidMass (scoreProbability (pilotScores τ)))
      (Finset.univ.filter (fun ν : Fin m → Fin n =>
        objective A b (pilotCenter A b (scoreProbability (pilotScores τ))
          (pilotProbability_nonneg (by omega) τ hτ) ν) ≤
        (1 + 2 / Real.sqrt ((1-1/8)*δ))^2 * objective A b xstar))

def lemma43 : Prop :=
  ∀ {Ω E S R : Type} [MeasurableSpace Ω] [MeasurableSpace E]
    [MeasurableSpace S] [MeasurableSpace R] [StandardBorelSpace R] {n : ℕ}
    (rules : StandardRules) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (source : Ω → S) (seed : Ω → E) (responses : Ω → Fin n → R)
    (p : Choices E n R) (hfresh : Fresh p) (hstop : Absorbing p)
    (hsource : Measurable source) (hseed : Measurable seed) (hresponses : Measurable responses)
    (hp : ∀ t,Measurable (p t))
    (hind : ProbabilityTheory.IndepFun (fun ω => (source ω,responses ω)) seed μ)
    (K : (t : ℕ) → History E n R t → Measure (S × (Fin n → R)))
    (hcond : ∀ t∈Finset.range n,ConditionalLaw μ (fun ω => (source ω,responses ω))
      (fun ω => history p seed responses ω t) (K t)) (κ : ℝ≥0∞)
    (hlocal : ∀ t∈Finset.range n,∀ᵐ h ∂μ.map (fun ω => history p seed responses ω t),
      ∀ j,p t h=Sum.inl j → information (K t h) Prod.fst (fun sb => sb.2 j) ≤ κ),
    information μ source (fun ω => history p seed responses ω n) ≤
      κ*∫⁻ ω,(queryCount p seed responses ω : ℝ≥0∞) ∂μ

def appendixA3 : Prop :=
  ∀ {n d : ℕ}
    (parametric : ParametricQuadraticSelection) (tikhonov : TikhonovConvergence)
    (A : Matrix (Fin n) (Fin d) ℝ) (w : Fin n → ℝ) (hw : ∀ i,0 ≤ w i),
    ∃ z : ℕ → (Fin n → ℝ) → Space d,
      (∀ k,Measurable (z k)) ∧
      (∀ k b,RegularizedMinimizer (euclideanHuber A w b) k (z k b) ∧
        ∀ x,RegularizedMinimizer (euclideanHuber A w b) k x → x=z k b) ∧
      (∀ b,Tendsto (fun k => z k b) atTop (nhds (minimumNormSelection A w b hw))) ∧
      Measurable (fun b => minimumNormSelection A w b hw)

end Paper29.ExpandedSpecification
