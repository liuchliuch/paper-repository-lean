import Paper36.MainEndpoints

/-! Corollary B.1 with precisely the source's realized-call certificates.
No approximation contract is imposed at unrealized model/oracle calls. -/
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

/-- Exact calibration and only the actual exploitation calls are certified. -/
def RealizedCertificates (α τ : ℝ) (c r : ℕ → S → A → ℝ) (ε ζ : ℕ → ℝ) (ω : Ω) : Prop :=
  ∀ n,
    (Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
      sampledRisk P α c n ω = minimumRisk α c (H+1) 0 s₀ (samples P n ω)) ∧
    (¬ Bank.calibrates (target (S := S) (A := A) (H := H) α) (fun j => deposit P α τ c j ω) n →
      sampledRisk P α c n ω ≤ τ + ε n ∧ sampledOptimum P α τ c r n ω - sampledReward P r n ω ≤ ζ n)

/-- Original Corollary B.1: only pathwise realized oracle calls carry error
certificates. The calibration step remains exact. -/
theorem corollary_B_1_realized_calls
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, minimumRisk α c (H+1) 0 s₀ q < τ)
    (O : BorelAlgorithm.BorelOracles α c r (H+1) s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (hcert : ∀ᵐ ω ∂μ, RealizedCertificates P α τ c r ε ζ ω) :
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
  · filter_upwards [hcert] with ω hω
    intro n
    refine ⟨?_, fun hn => ((hω n).2 hn).1⟩
    intro hn
    rw [(hω n).1 hn]
    simp only [deposit, Algorithm.deposits]
    ring
  · filter_upwards [hcert, support_ae P] with ω hω hs
    intro n
    refine ⟨?_, fun hn => ((hω n).2 hn).2⟩
    intro _
    have hu := (BorelAlgorithm.comparator_bounds O hr (samples P n ω)).2
    rw [BorelAlgorithm.comparator_eq_source O (hs.2 n)] at hu
    have hl := (Algorithm.reward_bounds r hr (policy P n ω) (samples P n ω) (H+1) 0 s₀).1
    change sampledOptimum P α τ c r n ω - sampledReward P r n ω ≤ (H+1 : ℝ)
    exact (sub_le_self _ hl).trans (by simpa only [Nat.cast_add, Nat.cast_one] using hu)
  · exact hK

/-- The one-stage constrained value is itself independent of the model. -/
lemma one_stage_value_model_independent (α τ : ℝ) (c r : ℕ → S → A → ℝ)
    (p q : Nested.Kernel S A) (s : S) :
    constrainedValue α c r 1 s τ p = constrainedValue α c r 1 s τ q := by
  unfold constrainedValue
  congr 1
  ext v
  simp_rw [Endpoints.one_stage_risk, Endpoints.one_stage_reward]

end
end Paper36.Main

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

/-- The original H=1 realized-call approximation contract. -/
theorem corollary_B_1_horizon_one_realized_calls
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (ε ζ : ℕ → ℝ) (hcert : ∀ᵐ ω ∂μ, RealizedCertificates P α τ c r ε ζ ω) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) ≤
      ∑ n ∈ Finset.range K, ζ n) := by
  have hpaths : ∀ᵐ ω ∂μ,
      Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ≤ ∑ n ∈ Finset.range K, ε n ∧
      Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ≤ ∑ n ∈ Finset.range K, ζ n := by
    filter_upwards [hcert] with ω hω
    have hnc (n : ℕ) : ¬ Bank.calibrates (target (S := S) (A := A) (H := 0) α)
        (fun j => deposit P α τ c j ω) n := by
      unfold target Bank.calibrates
      rw [SourceBank.horizon_one_target]
      simp only [(Bank.zero_target (fun j => deposit P α τ c j ω) n).1, lt_self_iff_false, not_false_eq_true]
    constructor
    · apply Finset.sum_le_sum
      intro n _
      have h := ((hω n).2 (hnc n)).1
      have hm := (Endpoints.one_stage_model_independent α c r (policy P n ω) (truth P ω) (samples P n ω) 0 s₀).1
      change trueRisk P α c n ω - τ ≤ ε n
      change trueRisk P α c n ω = sampledRisk P α c n ω at hm
      linarith
    · apply Finset.sum_le_sum
      intro n _
      have h := ((hω n).2 (hnc n)).2
      have hm := (Endpoints.one_stage_model_independent α c r (policy P n ω) (truth P ω) (samples P n ω) 0 s₀).2
      have hv := one_stage_value_model_independent α τ c r (truth P ω) (samples P n ω) s₀
      change optimum P α τ c r ω - trueReward P r n ω ≤ ζ n
      change trueReward P r n ω = sampledReward P r n ω at hm
      change optimum P α τ c r ω = sampledOptimum P α τ c r n ω at hv
      rw [hv, hm]
      exact h
  constructor
  · have hi := Assembly.integrable_total (fun n ω => trueRisk P α c n ω - τ)
      (fun n => (trueRisk_integrable P α hα hα1 c hc n).sub (integrable_const τ)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ε n)) (hpaths.mono (fun _ h => h.1))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh
  · have hi := Assembly.integrable_total (fun n ω => optimum P α τ c r ω - trueReward P r n ω)
      (fun n => (optimum_integrable P O hr).sub (trueReward_integrable P r hr n)) K
    have hh := integral_mono_ae hi (integrable_const (∑ n ∈ Finset.range K, ζ n)) (hpaths.mono (fun _ h => h.2))
    simpa only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul] using hh

/-- The exact H=1 conclusion for every realized exact-oracle choice, including
choices depending on the entire history and private randomization. -/
theorem theorem_4_2_horizon_one_realized_calls
    (α τ : ℝ) (hα : 0 < α) (hα1 : α ≤ 1)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (O : BorelAlgorithm.BorelOracles α c r 1 s₀ τ (support P))
    (hcert : ∀ᵐ ω ∂μ, RealizedCertificates P α τ c r (fun _ => 0) (fun _ => 0) ω) (K : ℕ) :
    ((∫ ω, Assembly.total (fun n ω => trueRisk P α c n ω - τ) K ω ∂μ) ≤ 0) ∧
    ((∫ ω, Assembly.total (fun n ω => optimum P α τ c r ω - trueReward P r n ω) K ω ∂μ) = 0) ∧
    (∀ ω, Bank.bank (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0 ∧
      Bank.count (target (S := S) (A := A) (H := 0) α) (fun j => deposit P α τ c j ω) K = 0) := by
  have hb := corollary_B_1_horizon_one_realized_calls P α τ hα hα1 c r hc hr O
    (fun _ => 0) (fun _ => 0) hcert K
  simp only [Finset.sum_const_zero] at hb
  refine ⟨hb.1, le_antisymm hb.2 ?_, ?_⟩
  · apply integral_nonneg_of_ae
    filter_upwards [hcert, support_ae P] with ω hω hs
    apply Finset.sum_nonneg
    intro n _
    have hnc : ¬ Bank.calibrates (target (S := S) (A := A) (H := 0) α)
        (fun j => deposit P α τ c j ω) n := by
      unfold target Bank.calibrates
      rw [SourceBank.horizon_one_target]
      simp only [(Bank.zero_target (fun j => deposit P α τ c j ω) n).1, lt_self_iff_false, not_false_eq_true]
    have hf := ((hω n).2 hnc).1
    have hm := (Endpoints.one_stage_model_independent α c r (policy P n ω) (truth P ω) (samples P n ω) 0 s₀).1
    have hft : risk α c (policy P n ω) (truth P ω) 1 0 s₀ ≤ τ := by
      change trueRisk P α c n ω = sampledRisk P α c n ω at hm
      simpa only [add_zero, ← hm] using hf
    have ho := O.exp_optimal (truth P ω) hs.1 (policy P n ω) hft
    rw [← Algorithm.constrainedValue_eq O.toOracles hs.1] at ho
    exact sub_nonneg.mpr ho
  · intro ω
    unfold target
    rw [SourceBank.horizon_one_target]
    exact Bank.zero_target _ K

end
end Paper36.Main
