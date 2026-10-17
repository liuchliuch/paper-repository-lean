import Paper36.MainExtensions

/-! The exact one-stage strengthening and the arbitrary-prior one-stage
approximation bound, with actual selected policies and actual constrained value. -/
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
  {μ : Measure Ω} [IsProbabilityMeasure μ] {s₀ : S}
  {E : EpisodeSystem μ Info S A 1 s₀}
  (P : PosteriorSystem (Model := Model) (Hist := Hist) E)

/-- The H=1 clause in Theorem 4.2 for the same arbitrary prior and protocol. -/
theorem theorem_4_2_horizon_one
    (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = Algorithm.selected O.toOracles
      (target (S := S) (A := A) (H := 0) α) (samples P) n ω) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0) := by
  have hh := SourceEndpoints.horizon_one_any_prior μ O.toOracles (samples P) (truth P) (support_ae P) K
  simpa only [Assembly.total, trueRisk, trueReward, optimum, ← hrun] using hh

lemma approximate_selected_one {α τ : ℝ} {c r : ℕ → S → A → ℝ} {ε ζ : ℕ → ℝ}
    (O' : Approximation.Oracles α c r 1 s₀ τ (support P) ε ζ) (n : ℕ) (ω : Ω) :
    Approximation.selected O' (target (S := S) (A := A) (H := 0) α) (samples P) n ω =
      O'.exploitation n (samples P n ω) := by
  unfold target
  rw [SourceBank.horizon_one_target]
  unfold Approximation.selected Bank.calibrates
  simp only [(Bank.zero_target (fun j => deposits α τ c 1 s₀ (samples P) j ω) n).1,
    lt_self_iff_false, if_false]

/-- The H=1 clause of Corollary B.1. No transition concentration is needed. -/
theorem corollary_B_1_horizon_one
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (ε ζ : ℕ → ℝ)
    (O' : Approximation.Oracles α c r 1 s₀ τ (support P) ε ζ)
    (hrun : ∀ n ω, policy P n ω = Approximation.selected O'
      (target (S := S) (A := A) (H := 0) α) (samples P) n ω) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  have hpaths : ∀ᵐ ω ∂μ,
      Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ≤ ∑ n ∈ Finset.range K, ε n ∧
      Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ≤ ∑ n ∈ Finset.range K, ζ n := by
    filter_upwards [support_ae P] with ω hω
    have hselected (n : ℕ) : policy P n ω = O'.exploitation n (samples P n ω) :=
      (hrun n ω).trans (approximate_selected_one P O' n ω)
    have hh := Endpoints.one_stage_approximate_oracles α τ c r (truth P ω) (fun n => samples P n ω)
      (fun n => policy P n ω) (O.exploitation (truth P ω)) 0 s₀ ε ζ
      (O.exp_feasible _ hω.1)
      (fun n => by
        change risk α c (policy P n ω) (samples P n ω) 1 0 s₀ ≤ τ + ε n
        rw [hselected]; exact O'.exp_risk n _ (hω.2 n))
      (fun n π hf => by
        have hv := O'.exp_reward n _ (hω.2 n)
        have ho := O.exp_optimal _ (hω.2 n) π hf
        rw [constrainedValue_eq O.toOracles (hω.2 n)] at hv
        change reward r π (samples P n ω) 1 0 s₀ ≤ reward r (policy P n ω) (samples P n ω) 1 0 s₀ + ζ n
        rw [hselected]
        exact ho.trans hv) K
    simpa only [Assembly.total, trueRisk, trueReward, optimum, constrainedValue_eq O.toOracles hω.1] using hh
  constructor
  · have hi := Assembly.integrable_total (fun n ω => trueRisk P α c n ω - τ)
      (fun n => (trueRisk_integrable P α hα hα1 c hc n).sub (integrable_const τ)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ε n)) (hpaths.mono (fun _ h => h.1))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh
  · have hi := Assembly.integrable_total (fun n ω => optimum P α τ c r ω - trueReward P r n ω)
      (fun n => (optimum_integrable P O hr).sub (trueReward_integrable P r hr n)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ζ n)) (hpaths.mono (fun _ h => h.2))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh

end
end Paper36.Main
