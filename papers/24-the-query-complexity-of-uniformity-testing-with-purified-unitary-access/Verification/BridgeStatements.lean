import PUT

/-!
# Genuine operator, probability and circuit obligations

These independently readable propositions cover actual semantic bridges.
They are supporting results. The actual principal source contracts are
independently specified in `Verification.PaperStatements`, with their
published standard inputs visible in their theorem types.
-/
noncomputable section
open MeasureTheory
namespace Verification.Specification

/-- The actual finite Fourier-weighted continuous linear operator has norm A,
provided the two source families have been constructed and shown orthonormal. -/
def ActualAdversaryNorm : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {d M : ℕ} (A : ℝ), 0 < A →
    ∀ (e : PUT.PhaseIndex d M → E) (f : PUT.PhaseIndex d M → F),
      Orthonormal ℂ e → Orthonormal ℂ f → ‖PUT.FiniteAdversary.gamma A e f‖ = A

/-- Equation (9) for actual full-space reflection query operators. -/
def ActualFullQueryNorm : Prop :=
  ∀ {E₀ E₁ F₀ F₁ : Type}
    [NormedAddCommGroup E₀] [InnerProductSpace ℂ E₀] [CompleteSpace E₀]
    [NormedAddCommGroup E₁] [InnerProductSpace ℂ E₁] [CompleteSpace E₁]
    [NormedAddCommGroup F₀] [InnerProductSpace ℂ F₀] [CompleteSpace F₀]
    [NormedAddCommGroup F₁] [InnerProductSpace ℂ F₁] [CompleteSpace F₁]
    (Γ : E₁ →L[ℂ] E₀) (ΓH : F₁ →L[ℂ] F₀)
    (V₀ : E₀ →ₗᵢ[ℂ] F₀) (V₁ : E₁ →ₗᵢ[ℂ] F₁),
    ‖PUT.OperatorBridge.liftedAdversary Γ ΓH ∘L
        PUT.OperatorBridge.reflectionBlock V₁.toContinuousLinearMap -
      PUT.OperatorBridge.reflectionBlock V₀.toContinuousLinearMap ∘L
        PUT.OperatorBridge.liftedAdversary Γ ΓH‖ ≤
      2 * (‖PUT.OperatorBridge.dplus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap‖ +
        ‖PUT.OperatorBridge.dminus Γ ΓH V₀.toContinuousLinearMap V₁.toContinuousLinearMap‖)

/-- Paley–Zygmund on an arbitrary probability measure, with actual integrals
and event mass; no finite approximation or assumed Cauchy–Schwarz premise. -/
def ContinuousPaleyZygmund : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → ℝ), Measurable Z → Integrable Z μ →
    Integrable (fun x => Z x ^ 2) μ →
    ∀ {m v : ℝ}, 0 < m → 0 < v →
      m ≤ ∫ x, Z x ∂μ → (∫ x, Z x ^ 2 ∂μ) ≤ v →
      m ^ 2 / (4 * v) ≤ μ.real {x | m / 2 ≤ Z x}

/-- A query-norm bound implies a bound on the actual complex progress change. -/
def ActualQueryProgress : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (Γ : F →L[ℂ] E) (U₀ : E ≃ₗᵢ[ℂ] E) (U₁ : F ≃ₗᵢ[ℂ] F)
    (x : E) (y : F), ‖x‖ = 1 → ‖y‖ = 1 →
    ∀ {B : ℝ}, ‖Γ.comp (U₁ : F →L[ℂ] F) - (U₀ : E →L[ℂ] E).comp Γ‖ ≤ B →
      ‖PUT.QueryModel.progress Γ (U₀ x) (U₁ y) - PUT.QueryModel.progress Γ x y‖ ≤ B

/-- The source's final Born-probability progress envelope (5). -/
def ActualFinalProgress : Prop :=
  ∀ {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (Γ : F →L[ℂ] E) (P₀ : PUT.QueryModel.Measurement E)
    (P₁ : PUT.QueryModel.Measurement F),
    (∀ y, P₀.reject (Γ y) = Γ (P₁.reject y)) →
    ∀ (x : E) (y : F), ‖x‖ = 1 → ‖y‖ = 1 → ∀ {A : ℝ}, ‖Γ‖ ≤ A →
      ‖PUT.QueryModel.progress Γ x y‖ ≤ A *
        (Real.sqrt ((1 - P₀.rejectionProbability x) * (1 - P₁.rejectionProbability y)) +
          Real.sqrt (P₀.rejectionProbability x * P₁.rejectionProbability y))

/-- The concrete phase reflection really prepares its specified vector in
an actual unitary model. -/
def ActualReflectionPreparation : Prop :=
  ∀ {d M : ℕ} (p : Fin d → ℝ) (θ : Fin d → Fin M → ℝ),
    0 < M → (∀ i, 0 ≤ p i) → ∑ i, p i = 1 →
      PUT.ReflectionOracle.unitary p θ (PUT.QueryModel.zeroState d M) =
        PUT.ReflectionOracle.euclid (PUT.vExt p M θ)

/-- Averaging the actual physical circuit over a continuous prior exactly
matches its latent Born probability. -/
def ActualPriorProbability : Prop :=
  ∀ {X H : Type} [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {μ : Measure X} [IsProbabilityMeasure μ]
    (C : PUT.QueryModel.Circuit H) (U : PUT.QueryModel.PointwiseUnitary μ H) (T : ℕ),
    (C.measurement.lift (μ := μ)).rejectionProbability ((C.priorEvolution U).state T) =
      ∫ x, C.rejectProbability (U.unitary x) T ∂μ

end Verification.Specification
