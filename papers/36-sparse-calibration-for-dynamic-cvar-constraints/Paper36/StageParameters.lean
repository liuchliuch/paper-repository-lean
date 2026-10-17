import Paper36.StageRealized
import Paper36.PolylogScaling

/-! Uniform multivariate parameter bounds for the actual B.3 algorithm. The
prior-induced stage gap controls tau without an extra budget restriction. -/
namespace Paper36.StageCalibration
open Set MeasureTheory Paper36.Regularity Paper36.Nested
noncomputable section
variable {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]

/-- The source's actual maximum minimum stage risk lies in [0,H]. -/
theorem max_minimumRisk_bounds (ν : Measure (Nested.Kernel S A)) [IsProbabilityMeasure ν]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S) :
    0 ≤ sSup (minimumRisk β c H 0 s₀ '' ν.support) ∧
      sSup (minimumRisk β c H 0 s₀ '' ν.support) ≤ H := by
  have hrange (q : Nested.Kernel S A) : minimumRisk β c H 0 s₀ q ∈ Icc 0 (H:ℝ) := by
    rw [minimumRisk_eq_dp β hβ c hc q H 0 s₀]
    exact dp_bounds β hβ c hc (RiskBridge.ofKernel q) H 0 s₀
  have hν : ν ≠ 0 := by
    intro hz
    have hm : ν Set.univ = 1 := measure_univ
    simp [hz] at hm
  obtain ⟨q,hq⟩ := ν.nonempty_support hν
  have hbound : BddAbove (minimumRisk β c H 0 s₀ '' ν.support) := by
    refine ⟨H, ?_⟩
    rintro _ ⟨p,_,rfl⟩
    exact (hrange p).2
  constructor
  · exact (hrange q).1.trans (le_csSup hbound (Set.mem_image_of_mem _ hq))
  · apply csSup_le ⟨_,Set.mem_image_of_mem _ hq⟩
    rintro _ ⟨p,_,rfl⟩
    exact (hrange p).2

/-- In particular the original budget satisfies tau <= Delta_*+H for B.3. -/
theorem induced_gap_budget_bound (ν : Measure (Nested.Kernel S A)) [IsProbabilityMeasure ν]
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (τ : ℝ) (H : ℕ)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Icc 0 1) (s₀ : S) :
    τ ≤ uniformGap ν β c H s₀ τ + H := by
  have hb := max_minimumRisk_bounds ν β hβ H c hc s₀
  unfold uniformGap
  linarith [hb.2]

end
end Paper36.StageCalibration

namespace Paper36.StageMain
open MeasureTheory ProbabilityTheory Paper36.Regularity Paper36.Nested Paper36.StageAlgorithm
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

lemma actual_gap_budget_bound (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (τ : ℝ) (c : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1) :
    τ ≤ delta P β τ c + (H+1 : ℝ) := by
  letI : IsProbabilityMeasure (actualPrior P) :=
    Measure.isProbabilityMeasure_map ((decode_measurable P).comp P.latent_meas).aemeasurable
  have hb := StageCalibration.induced_gap_budget_bound (actualPrior P) β hβ τ (H+1) c hc s₀
  simpa only [delta,Nat.cast_add,Nat.cast_one] using hb

/-- The B.3 reward soft-O statement as an actual uniform regret inequality. -/
theorem reward_parameter_bound
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω)
    (hH : 1 ≤ H) {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, Assembly.total (fun n ω => optimum P β τ c r ω-trueReward P r n ω) K ω ∂μ) ≤
      (Fintype.card S : ℝ)*Real.sqrt (Fintype.card A)*
        (((H+1:ℕ):ℝ)*Real.sqrt (H+1)+((H+1:ℕ):ℝ)*Real.sqrt (Weights.stageWsq β (H+1))/delta P β τ c)*
          Real.sqrt (K:ℝ)*PolylogScaling.rewardPolylog (Fintype.card S) (Fintype.card A) (H+1) K := by
  letI : IsProbabilityMeasure (actualPrior P) :=
    Measure.isProbabilityMeasure_map ((decode_measurable P).comp P.latent_meas).aemeasurable
  have hg := StageAlgorithm.induced_gap_parameters (actualPrior P) β hβ τ c hc (H+1) s₀ hstrict
  have hd := SourceBank.dimensions (A:=A) s₀ (show 1≤H+1 by omega)
  have htau : τ ≤ delta P β τ c+((H+1:ℕ):ℝ) := by
    simpa only [Nat.cast_add,Nat.cast_one] using actual_gap_budget_bound P β hβ τ c hc
  have hp := PolylogScaling.reward_performance_uniform hd.1 hd.2.1 hd.2.2
    (PolylogScaling.horizon_le_stageW β hβ (show 2≤H+1 by omega)) hg.1 htau hK
  have hm := (theorem_4_2 P external β τ hβ hτ c r hc hr hstrict O hrun K hK).2.1
  apply hm.trans
  simpa only [rewardAllowance,target,StageCharging.stageTarget,Nat.cast_add,Nat.cast_one] using hp

/-- The B.3 risk soft-O statement with an explicit K-independent polylog. -/
theorem risk_parameter_bound
    (external : RowTapes.ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (τ : ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (hτ : 0 ≤ τ)
    (c r : ℕ → S → A → ℝ) (hc : ∀ h s a, c h s a ∈ Set.Icc 0 1)
    (hr : ∀ h s a, r h s a ∈ Set.Icc 0 1)
    (hstrict : ∀ q ∈ support P, ∃ π : Simulation.Policy S A,
      StageRisk.risk β c π (RiskBridge.ofKernel q) (H+1) 0 s₀ < τ)
    (O : StageAlgorithm.BorelOracles β c r (H+1) s₀ τ (support P))
    (hrun : ∀ n ω, policy P n ω = StageAlgorithm.selected O.toOracles
      (target (S := S) (A := A) (H := H) β) (samples P) n ω)
    {K : ℕ} (hK : 1 ≤ K) :
    (∫ ω, Assembly.total (fun n ω => trueRisk P β c n ω-τ) K ω ∂μ) ≤
      lowConstant (S:=S) (A:=A) (H:=H) β+
        16*(Fintype.card S:ℝ)^2*(Fintype.card A:ℝ)*(Real.sqrt (Weights.stageWsq β (H+1)))^2/delta P β τ c*
          (PolylogScaling.F (Fintype.card S) (Fintype.card A) (H+1)
            (Real.sqrt (Weights.stageWsq β (H+1))) (delta P β τ c))^2 := by
  letI : IsProbabilityMeasure (actualPrior P) :=
    Measure.isProbabilityMeasure_map ((decode_measurable P).comp P.latent_meas).aemeasurable
  have hg := StageAlgorithm.induced_gap_parameters (actualPrior P) β hβ τ c hc (H+1) s₀ hstrict
  have hd := SourceBank.dimensions (A:=A) s₀ (show 1≤H+1 by omega)
  have hp := PolylogScaling.residual_uniform hd.1 hd.2.1 hd.2.2
    (Real.sqrt_nonneg (Weights.stageWsq β (H+1))) hg.1
  have hm := (theorem_4_2 P external β τ hβ hτ c r hc hr hstrict O hrun K hK).1
  apply hm.trans
  simpa only [riskEnvelope,StageCharging.stageResidual,Nat.cast_add,Nat.cast_one] using
    add_le_add_left hp (lowConstant (S:=S) (A:=A) (H:=H) β)

end
end Paper36.StageMain
