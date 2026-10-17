import Paper36.Main
import Paper36.SourceEndpoints

/-! The simultaneous pathwise calibration assertion, the risk-bank consequent
of the fixed-pair certificate, and certified approximate exploitation. -/
namespace Paper36.Main
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.Algorithm
  Paper36.StatisticalCounts Paper36.Statistical
open scoped BigOperators
noncomputable section
universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {H : ℕ} {s₀ : S}
  {E : EpisodeSystem μ Info S A (H+1) s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

/-- (4.12) and almost-sure sparsity on one common event, simultaneously for all K. -/
theorem pathwise_calibration
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ) :
    0 < delta P α τ c ∧
    ∀ᵐ ω ∂μ,
      (∀ K, (Bank.count (target (S := S) (A := A) (H := H) α)
        (fun j => deposit P α τ c j ω) K : ℝ) ≤
        min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) ∧
      Filter.Tendsto (fun K : ℕ =>
        (Bank.count (target (S := S) (A := A) (H := H) α)
          (fun j => deposit P α τ c j ω) K : ℝ) / (K : ℝ)) Filter.atTop (nhds 0) := by
  have hg := PosteriorAlgorithm.gap_positive _ (decode_measurable P) _ P.latent_meas
    α τ hα hα1 (H+1) c hc s₀ hstrict
  refine ⟨hg.1, ?_⟩
  filter_upwards [support_ae P] with ω hω
  exact ⟨fun K => SourceBank.calibration_count α τ (delta P α τ c) hα hg.1 hτ c hc
    (H+1) (by omega) s₀ (support P) hg.2 (samples P) ω hω.2 K,
    SourceBank.calibration_sparse α τ (delta P α τ c) hα hg.1 hτ c hc (H+1) (by omega)
      s₀ (support P) hg.2 (samples P) ω hω.2⟩

/-- Equation (5.12) with exactly the fixed (K,delta) probability from (5.11).
The event concerns the same true nested-risk values and actual observed bank. -/
theorem risk_bank_certificate
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Weights.W α (H+1)) (Weights.w α (H+1)) δ K -
          Bank.bank (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω} ≤ δ := by
  have hstat := PosteriorSystem.theorem_5_6 E P external α hα hα1 c hc ℱ hinfo hpath hK hδ hδ1
  have hsubset : {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Weights.W α (H+1)) (Weights.w α (H+1)) δ K -
          Bank.bank (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) K <
        Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω} ≤ᵐ[μ]
      {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
        (Weights.W α (H+1)) (Weights.w α (H+1)) δ K < ∑ k ∈ Finset.range K, P.riskError α c k ω} := by
    filter_upwards [support_ae P] with ω hω
    intro herr
    have hb := Algorithm.risk_bank_certificate_path O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) (truth P) ω hω.2 K
      (∑ n ∈ Finset.range K, (trueRisk P α c n ω - sampledRisk P α c n ω)) (by simp only [← hrun]; exact le_rfl)
    simp only [← hrun] at hb
    have he : (∑ n ∈ Finset.range K, (trueRisk P α c n ω - sampledRisk P α c n ω)) =
        ∑ n ∈ Finset.range K, P.riskError α c n ω := by
      apply Finset.sum_congr rfl
      intro n _
      exact (riskError_eq P α hα hα1 c hc n ω).symm
    change _ < _ at herr ⊢
    change Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ≤ _ at hb
    rw [he] at hb
    linarith
  exact (ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsubset)).trans hstat

/-- Corollary B.1 for the actual approximate execution rule. Its errors are
one-call deterministic certificates, and appear once in the cumulative result. -/
theorem corollary_B_1
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (O' : Approximation.Oracles α c r (H+1) s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = Approximation.selected O'
      (target (S := S) (A := A) (H := H) α) (samples P) n ω) :
    ∀ K, 1 ≤ K →
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.riskEnvelope (S := S) (A := A) α (delta P α τ c) (H+1) + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      rewardAllowance (S := S) (A := A) (H := H) K + (H+1 : ℝ) *
        ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c) + ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, Assembly.countRV (target (S := S) (A := A) (H := H) α) (deposit P α τ c) K ω ∂μ) ≤
      min (K : ℝ) ((target (S := S) (A := A) (H := H) α K + τ) / delta P α τ c)) := by
  intro K hK
  apply certified_performance P external α τ hα hα1 hτ c r hc hr hstrict O ε ζ hε hζ
  · filter_upwards [support_ae P] with ω hω
    intro n
    simpa only [sampledRisk, hrun] using
      Approximation.sampled_risk O' (target (S := S) (A := A) (H := H) α) (samples P) n ω (hω.2 n)
  · filter_upwards [support_ae P] with ω hω
    intro n
    simpa only [sampledOptimum, sampledReward, hrun, Nat.cast_add, Nat.cast_one] using
      Approximation.sampled_reward O' O.toOracles hr (target (S := S) (A := A) (H := H) α)
        (samples P) n ω (hω.2 n)
  · exact hK

end
end Paper36.Main
