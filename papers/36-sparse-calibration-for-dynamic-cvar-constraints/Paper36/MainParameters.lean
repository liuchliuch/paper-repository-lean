import Paper36.MainRealized
import Paper36.PolylogScaling
import Paper36.GapBounds

/-! The literal multivariate parameter envelopes of Theorem 4.2, with every
hidden polylog factor displayed. The budget term is absorbed using the actual
prior-induced gap, not an additional restriction on tau. -/
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

lemma actual_gap_budget_bound (α τ : ℝ) (hα : 0 ≤ α)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) :
    τ ≤ delta P α τ c + (H+1 : ℝ) := by
  letI : IsProbabilityMeasure (PosteriorAlgorithm.prior (μ:=μ) (decode P) P.latent) :=
    Measure.isProbabilityMeasure_map ((decode_measurable P).comp P.latent_meas).aemeasurable
  have hb := Prior.induced_gap_budget_bounds (PosteriorAlgorithm.prior (μ:=μ) (decode P) P.latent)
    α τ hα (H+1) c hc s₀
  simpa only [delta, PosteriorAlgorithm.gap, Nat.cast_add, Nat.cast_one] using hb.2.2

/-- Source multivariate soft-O reward scaling, as a uniform explicit inequality
on the actual signed regret, with a multiplier consisting only of logarithms. -/
theorem reward_parameter_bound
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω)
    (hH : 1 ≤ H) {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      (Fintype.card S : ℝ) * Real.sqrt (Fintype.card A) *
        (((H+1 : ℕ) : ℝ) * Real.sqrt (H+1) + ((H+1 : ℕ) : ℝ) * Weights.W α (H+1) / delta P α τ c) *
          Real.sqrt (K:ℝ) * PolylogScaling.rewardPolylog (Fintype.card S) (Fintype.card A) (H+1) K := by
  have hg := PosteriorAlgorithm.gap_positive _ (decode_measurable P) _ P.latent_meas
    α τ hα hα1 (H+1) c hc s₀ hstrict
  have hd := SourceBank.dimensions (A:=A) s₀ (show 1≤H+1 by omega)
  have htau : τ ≤ delta P α τ c + ((H+1:ℕ):ℝ) := by
    simpa only [Nat.cast_add, Nat.cast_one] using actual_gap_budget_bound P α τ hα.le c hc
  have hp := PolylogScaling.reward_performance_uniform hd.1 hd.2.1 hd.2.2
    (PolylogScaling.horizon_le_W hα hα1 (show 2≤H+1 by omega)) hg.1 htau hK
  have hm := (theorem_4_2 P external α τ hα hα1 hτ c r hc hr hstrict O hrun K hK).2.1
  apply hm.trans
  simpa only [rewardAllowance, target, SourceBank.target, Nat.cast_add, Nat.cast_one] using hp

/-- Source risk-envelope scaling, with an explicit K-independent polylog
factor and the literal SAH*w and S^2*A*W^2/Delta parameter exponents. -/
theorem risk_parameter_bound
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) α) (samples P) n ω)
    {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤
      SourceBank.lowConstant (S := S) (A := A) α (H+1) +
      16 * (Fintype.card S : ℝ)^2 * (Fintype.card A : ℝ) * (Weights.W α (H+1))^2 / delta P α τ c *
        (PolylogScaling.F (Fintype.card S) (Fintype.card A) (H+1) (Weights.W α (H+1)) (delta P α τ c))^2 := by
  have hg := PosteriorAlgorithm.gap_positive _ (decode_measurable P) _ P.latent_meas
    α τ hα hα1 (H+1) c hc s₀ hstrict
  have hd := SourceBank.dimensions (A:=A) s₀ (show 1≤H+1 by omega)
  have hp := PolylogScaling.residual_uniform hd.1 hd.2.1 hd.2.2 (Weights.W_nonneg α (H+1)) hg.1
  have hm := (theorem_4_2 P external α τ hα hα1 hτ c r hc hr hstrict O hrun K hK).1
  apply hm.trans
  simpa only [SourceBank.riskEnvelope, SourceBank.residual, Nat.cast_add, Nat.cast_one] using
    add_le_add_left hp (SourceBank.lowConstant (S:=S) (A:=A) α (H+1))

end
end Paper36.Main
