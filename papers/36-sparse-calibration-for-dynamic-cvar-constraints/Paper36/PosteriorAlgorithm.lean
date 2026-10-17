import Paper36.BorelAlgorithm
import Paper36.Posterior

/-! Prior support, induced uniform gap, and comparator symmetry for the actual
algorithm. Arbitrary model encodings are decoded into the physical kernel simplex;
no identifiability, factorization, or posterior concentration is assumed. -/
namespace Paper36.PosteriorAlgorithm
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
noncomputable section
variable {S A Ω Model Hist : Type*} [Fintype S] [Fintype A] [Nonempty A]
  [MeasurableSpace Ω] [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model]
  [MeasurableSpace Hist] {μ : Measure Ω} [IsProbabilityMeasure μ]

def prior (decode : Model → Kernel S A) (latent : Ω → Model) : Measure (Kernel S A) :=
  μ.map (fun ω => decode (latent ω))

def gap (decode : Model → Kernel S A) (latent : Ω → Model)
    (α τ : ℝ) (c : ℕ → S → A → ℝ) (H : ℕ) (s₁ : S) : ℝ :=
  τ - sSup (minimumRisk α c H 0 s₁ '' (prior (μ := μ) decode latent).support)

/-- A posterior draw lies on the same actual kernel support as the latent kernel,
simultaneously for all episodes. Equality of posterior laws is enough. -/
theorem posterior_support (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent : Ω → Model) (hlatent : Measurable latent)
    (sampled : ℕ → Ω → Model) (hsampled : ∀ k, Measurable (sampled k))
    (history : ℕ → Ω → Hist) (hhistory : ∀ k, Measurable (history k))
    (hposterior : ∀ k, condDistrib latent (history k) μ =ᵐ[μ.map (history k)]
      condDistrib (sampled k) (history k) μ) :
    ∀ᵐ ω ∂μ, decode (latent ω) ∈ (prior (μ := μ) decode latent).support ∧
      ∀ k, decode (sampled k ω) ∈ (prior (μ := μ) decode latent).support := by
  have hp : Measurable (fun ω => decode (latent ω)) := hdecode.comp hlatent
  have htrue : ∀ᵐ ω ∂μ, decode (latent ω) ∈ (prior (μ := μ) decode latent).support :=
    ae_of_ae_map hp.aemeasurable (Measure.support_mem_ae (μ := prior (μ := μ) decode latent))
  have hsample : ∀ k, ∀ᵐ ω ∂μ, decode (sampled k ω) ∈ (prior (μ := μ) decode latent).support := by
    intro k
    have hd := (Posterior.posterior_joint_identDistrib (hhistory k).aemeasurable
      hlatent.aemeasurable (hsampled k).aemeasurable (hposterior k)).comp
      (hdecode.comp measurable_snd)
    exact hd.ae_mem_snd (Measure.isClosed_support.measurableSet) htrue
  filter_upwards [htrue, ae_all_iff.2 hsample] with ω ht hs
  exact ⟨ht, hs⟩

/-- Lemma 2.1's positive induced gap for the arbitrary decoded prior. -/
theorem gap_positive (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent : Ω → Model) (hlatent : Measurable latent)
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) (s₁ : S)
    (hstrict : ∀ q ∈ (prior (μ := μ) decode latent).support, minimumRisk α c H 0 s₁ q < τ) :
    0 < gap (μ := μ) decode latent α τ c H s₁ ∧
      ∀ q ∈ (prior (μ := μ) decode latent).support,
        minimumRisk α c H 0 s₁ q ≤ τ - gap (μ := μ) decode latent α τ c H s₁ := by
  letI : IsProbabilityMeasure (prior (μ := μ) decode latent) :=
    Measure.isProbabilityMeasure_map (hdecode.comp hlatent).aemeasurable
  have hg := Prior.lemma_2_1 (prior (μ := μ) decode latent) α hα hα1 H c hc s₁ τ hstrict
  refine ⟨hg.1, ?_⟩
  intro q hq
  have h := hg.2 q hq
  change gap (μ := μ) decode latent α τ c H s₁ ≤ τ - minimumRisk α c H 0 s₁ q at h
  linarith

/-- Equation (5.18) for the actual constrained comparator and arbitrary prior. -/
theorem comparator_symmetry (decode : Model → Kernel S A) (hdecode : Measurable decode)
    (latent sampled : Ω → Model) (hlatent : Measurable latent) (hsampled : Measurable sampled)
    (history : Ω → Hist) (hhistory : Measurable history)
    (hposterior : condDistrib latent history μ =ᵐ[μ.map history] condDistrib sampled history μ)
    {α τ : ℝ} {c r : ℕ → S → A → ℝ} {H : ℕ} {s₁ : S}
    {Q : Set (Kernel S A)} (O : BorelAlgorithm.BorelOracles α c r H s₁ τ Q)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hsupport : ∀ᵐ ω ∂μ, decode (latent ω) ∈ Q ∧ decode (sampled ω) ∈ Q) :
    (∫ ω, constrainedValue α c r H s₁ τ (decode (latent ω)) -
      constrainedValue α c r H s₁ τ (decode (sampled ω)) ∂μ) = 0 := by
  have hm := (BorelAlgorithm.measurable_comparator O).comp hdecode
  have he := Posterior.posterior_expectation_eq hhistory.aemeasurable hlatent.aemeasurable
    hsampled.aemeasurable hposterior (hm.comp measurable_snd)
  have hli := BorelAlgorithm.integrable_comparator μ O hr (fun ω => decode (latent ω)) (hdecode.comp hlatent)
  have hsi := BorelAlgorithm.integrable_comparator μ O hr (fun ω => decode (sampled ω)) (hdecode.comp hsampled)
  have hcongr : (fun ω => constrainedValue α c r H s₁ τ (decode (latent ω)) -
      constrainedValue α c r H s₁ τ (decode (sampled ω))) =ᵐ[μ]
      (fun ω => BorelAlgorithm.comparator O (decode (latent ω)) -
        BorelAlgorithm.comparator O (decode (sampled ω))) := by
    filter_upwards [hsupport] with ω hω
    rw [← BorelAlgorithm.comparator_eq_source O hω.1, ← BorelAlgorithm.comparator_eq_source O hω.2]
  rw [integral_congr_ae hcongr, integral_sub hli hsi]
  simpa only [sub_eq_zero] using he

end
end Paper36.PosteriorAlgorithm
