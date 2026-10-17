import Paper36.Statistical
import Paper36.StageCharging
import Paper36.StageCalibration

/-! The B.3 statistical inheritance. It uses exactly the same posterior,
trajectory, tape and count experiment as the constant-risk results. Only the
actual StageRisk recursion and the source prefix weights are changed. -/
namespace Paper36.Statistical
open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory Paper36.CVaR Paper36.Simulation
  Paper36.Trajectories Paper36.RowTapes Paper36.StatisticalCounts
noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {S A : Type u} [Fintype S] [Fintype A] [Nonempty S] [Nonempty A]
  [DecidableEq S] [DecidableEq A] [MeasurableSpace S] [DiscreteMeasurableSpace S]
  {Ω Info Model Hist : Type*} [MeasurableSpace Ω] [MeasurableSpace Info]
  [MeasurableSpace Model] [StandardBorelSpace Model] [Nonempty Model] [MeasurableSpace Hist]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ} {s₀ : S}

local instance stagePolicyKernel_opens : OpensMeasurableSpace (Nested.Policy S A × Nested.Kernel S A) :=
  @Prod.opensMeasurableSpace _ _ _ _ _ _ inferInstance inferInstance inferInstance

lemma measurable_stageRisk (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S) :
    Measurable (fun ω => StageRisk.risk β c (π ω) (p ω) n h s) := by
  have hm := (StageCalibration.continuous_actualRisk β hβ c hc n h s).measurable.comp
    ((Measurability.measurable_regularPolicy π hπ).prodMk (Measurability.measurable_regularKernel p hp))
  simpa only [Function.comp_def, Measurability.of_regularPolicy, Measurability.of_regularKernel] using hm

lemma integrable_stageRisk (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (π : Ω → Simulation.Policy S A) (p : Ω → Simulation.Kernel S A)
    (hπ : ∀ h s a, Measurable (fun ω => (π ω h s).mass a))
    (hp : ∀ s a t, Measurable (fun ω => (p ω s a).mass t)) (n h : ℕ) (s : S) :
    Integrable (fun ω => StageRisk.risk β c (π ω) (p ω) n h s) μ := by
  apply Integrable.of_bound (measurable_stageRisk β hβ c hc π p hπ hp n h s).aestronglyMeasurable n
  apply ae_of_all
  intro ω
  have hb := StageRisk.risk_bounds β hβ c hc (π ω) (p ω) n h s
  simpa only [Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2

namespace PosteriorSystem
variable {E : EpisodeSystem μ Info S A T s₀} (P : PosteriorSystem (Model := Model) (Hist := Hist) E)
theorem masked_stage_risk_bound {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀)
    (P' : PosteriorSystem (Model := Model) (Hist := Hist) E')
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (K : ℕ) (ω : Ω) :
    (∑ k ∈ Finset.range K, if ω ∈ P'.goodKL Λ k then
      (StageRisk.risk β c (P'.policies ω k) (E'.latent ω) (H+1) 0 s₀ -
        StageRisk.risk β c (P'.policies ω k) (P'.sampledKernels ω k) (H+1) 0 s₀) else 0) ≤
      Weights.stagew β (H+1) * HybridCharging.Ylo (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) *
        HybridCharging.Yhi (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H) := by
  classical
  apply StageCharging.masked_risk_hybrid_sum_bound_stage β hβ c hc
    (P'.policies ω) (E'.latent ω) (P'.sampledKernels ω) s₀ (P'.counts ω) hΛ K H
    (fun k => ω ∈ P'.goodKL Λ k)
  intro k _ hg s a hn
  exact P'.goodKL_radius hΛ k ω hg (s,a) (by omega)

def stageRiskError (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (k : ℕ) (ω : Ω) : ℝ :=
  StageRisk.risk β c (P.policies ω k) (E.latent ω) T 0 s₀ -
    StageRisk.risk β c (P.policies ω k) (P.sampledKernels ω k) T 0 s₀

def maskedStageRisk (β : ℕ → ℝ) (c : ℕ → S → A → ℝ) (Λ : ℝ) (K : ℕ) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range K, (P.goodKL Λ k).indicator (P.stageRiskError β c k) ω

lemma stageRiskError_integrable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) (k : ℕ) :
    Integrable (P.stageRiskError β c k) μ := by
  exact (integrable_stageRisk β hβ c hc (fun ω => P.policies ω k) E.latent
    (P.policy_mass_measurable k) P.true_mass_measurable T 0 s₀).sub
    (integrable_stageRisk β hβ c hc (fun ω => P.policies ω k)
      (fun ω => P.sampledKernels ω k) (P.policy_mass_measurable k)
      (P.sampled_mass_measurable k) T 0 s₀)

lemma stageRiskError_upper (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (k : ℕ) (ω : Ω) : P.stageRiskError β c k ω ≤ T := by
  have hp := StageRisk.risk_bounds β hβ c hc (P.policies ω k) (E.latent ω) T 0 s₀
  have hq := StageRisk.risk_bounds β hβ c hc (P.policies ω k) (P.sampledKernels ω k) T 0 s₀
  dsimp [stageRiskError]
  linarith [hp.2, hq.1]

lemma maskedStageRisk_integrable (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1)
    (c : ℕ → S → A → ℝ) (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) (Λ : ℝ) (K : ℕ) :
    Integrable (P.maskedStageRisk β c Λ K) μ :=
  integrable_finset_sum _ fun k _ =>
    (P.stageRiskError_integrable β hβ c hc k).indicator (P.goodKL_measurable Λ k)

/-- The complete expected confidence-failure allowance: it is at most T/4,
so the paper's convenient T/2 allowance is retained without changing its constant. -/
theorem stage_risk_expectation_le_masked
    (external : ExternalCategoricalConcentration (S := S)) (hT : 1 ≤ T)
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P.stageRiskError β c k ω ∂μ) ≤
      (∫ ω, P.maskedStageRisk β c (klThreshold (Fintype.card S) (K*T) (P.expectedBudget K)) K ω ∂μ) +
        (T : ℝ)/4 := by
  let Λ := klThreshold (Fintype.card S) (K*T) (P.expectedBudget K)
  have hstep : ∀ k < K, (∫ ω, P.stageRiskError β c k ω ∂μ) ≤
      (∫ ω, (P.goodKL Λ k).indicator (P.stageRiskError β c k) ω ∂μ) +
        (T : ℝ) * (1 / (4 * (K : ℝ))) := by
    intro k hk
    have hi := integral_le_masked_add_failure (P.stageRiskError_integrable β hβ c hc k)
      (P.goodKL Λ k) (P.goodKL_measurable Λ k) (Nat.cast_nonneg T)
      (P.stageRiskError_upper β hβ c hc k)
    have hp := P.current_kl_failure_probability external hT hK k hk
    exact hi.trans (add_le_add_left (mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg T)) _)
  calc
    _ ≤ ∑ k ∈ Finset.range K,
        ((∫ ω, (P.goodKL Λ k).indicator (P.stageRiskError β c k) ω ∂μ) +
          (T : ℝ) * (1 / (4 * (K : ℝ)))) :=
      Finset.sum_le_sum fun k hk => hstep k (Finset.mem_range.mp hk)
    _ = (∫ ω, P.maskedStageRisk β c Λ K ω ∂μ) + (T : ℝ)/4 := by
      rw [Finset.sum_add_distrib]
      rw [show (∫ ω, P.maskedStageRisk β c Λ K ω ∂μ) =
        ∑ k ∈ Finset.range K, ∫ ω, (P.goodKL Λ k).indicator (P.stageRiskError β c k) ω ∂μ from
        integral_finset_sum _ (fun k _ =>
          (P.stageRiskError_integrable β hβ c hc k).indicator (P.goodKL_measurable Λ k))]
      congr 1
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
      field_simp


section StageSourceHorizon
variable {H : ℕ} (E' : EpisodeSystem μ Info S A (H+1) s₀)
  (P' : PosteriorSystem (Model := Model) (Hist := Hist) E')

theorem stage_risk_expectation_bound_raw
    (external : ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P'.stageRiskError β c k ω ∂μ) ≤
      2 * (Fintype.card (S × A) : ℝ) * (H+1) * Weights.stagew β (H+1) +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt
        (klThreshold (Fintype.card S) (K*(H+1)) (P'.expectedBudget K) * (K : ℝ) *
          (2 * (Fintype.card (S × A) : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * (H+1)))) +
      (H+1 : ℝ) / 4 := by
  let Λ := klThreshold (Fintype.card S) (K*(H+1)) (P'.expectedBudget K)
  have hΛ : 0 ≤ Λ := klThreshold_nonneg _ _ (P'.expectedBudget_one_le (by omega) hK)
  have hpath : ∀ᵐ ω ∂μ, P'.maskedStageRisk β c Λ K ω ≤
      Weights.stagew β (H+1) * HybridCharging.Ylo (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) *
        HybridCharging.Yhi (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H) := by
    apply ae_of_all
    intro ω
    simpa only [maskedStageRisk, stageRiskError, Set.indicator_apply] using
      masked_stage_risk_bound E' P' β hβ c hc hΛ K ω
  have hexpect := HybridCharging.expected_charging_bound μ
    (P'.maskedStageRisk_integrable β hβ c hc Λ K) (E'.Ylo_integrable K) (E'.Yhi_integrable K)
    (ae_of_all _ fun ω => E'.Yhi_nonneg K ω) (Real.sqrt_nonneg (Weights.stageWsq β (H+1))) hΛ K hpath
  have hlow := mul_le_mul_of_nonneg_left (E'.integral_Ylo_le K) (StageCharging.stagew_nonneg β (H+1))
  have hhigh := mul_le_mul_of_nonneg_left
    (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (E'.integral_Yhi_le hK)
      (show 0 ≤ Λ * (K : ℝ) by positivity)))
    (show 0 ≤ 4 * Real.sqrt (Weights.stageWsq β (H+1)) from mul_nonneg (by norm_num) (Real.sqrt_nonneg (Weights.stageWsq β (H+1))))
  have hmask := hexpect.trans (add_le_add hlow hhigh)
  have hfail := P'.stage_risk_expectation_le_masked external (by omega) β hβ c hc hK
  change _ ≤ _
  dsimp [Λ] at hmask
  have htotal := hfail.trans (add_le_add_right hmask (((H+1 : ℕ) : ℝ) / 4))
  -- The next line only normalizes products and the natural horizon cast.
  convert htotal using 1 <;> simp only [Nat.cast_add, Nat.cast_one] <;> ring

/-- The full fixed-K certificate before substituting the prescribed delta
budget. The only exceptional terms are the proved posterior-row union bound
and the two applications of the proved predictable-to-realized conversion. -/
theorem stage_risk_certificate_probability_raw
    (external : ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E'.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E'.path k))
    {K : ℕ} (hK : 1 ≤ K) {budget ell : ℝ} (hb : 1 ≤ budget) (hell : 0 < ell) :
    μ.real {ω | Weights.stagew β (H+1) *
        (4 * (Fintype.card (S × A) : ℝ) * (H+1) + 2 * (H+1) * ell) +
      4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt
        (klThreshold (Fintype.card S) (K*(H+1)) budget * (K : ℝ) *
          (4 * (Fintype.card (S × A) : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * (H+1)) + 2 * ell)) <
      ∑ k ∈ Finset.range K, P'.stageRiskError β c k ω} ≤
      2 * (K : ℝ) * ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) +
        2 * Real.exp (-ell) := by
  let Λ := klThreshold (Fintype.card S) (K*(H+1)) budget
  let Bconf : Set Ω := ⋃ k ∈ Finset.range K, (P'.goodKL Λ k)ᶜ
  let Blow := 4 * (Fintype.card (S × A) : ℝ) * (H+1) + 2 * (H+1) * ell
  let Bhi := 4 * (Fintype.card (S × A) : ℝ) * Real.log (Real.exp 1 * (K : ℝ) * (H+1)) + 2 * ell
  let Ylo := fun ω => HybridCharging.Ylo (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H
  let Yhi := fun ω => HybridCharging.Yhi (P'.policies ω) (E'.latent ω) s₀ (P'.counts ω) K H
  let Btotal : Set Ω := Bconf ∪ ({ω | Blow < Ylo ω} ∪ {ω | Bhi < Yhi ω})
  have hΛ : 0 ≤ Λ := klThreshold_nonneg _ _ hb
  have hconf : μ.real Bconf ≤ 2 * (K : ℝ) *
      ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) := by
    apply (measureReal_biUnion_finset_le (Finset.range K) (fun k => (P'.goodKL Λ k)ᶜ)).trans
    calc
      _ ≤ ∑ _k ∈ Finset.range K, 2 *
          ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) := by
        apply Finset.sum_le_sum
        intro k hk
        simpa only [Nat.cast_add, Nat.cast_one] using
          P'.current_kl_failure_probability_budget external K k (Finset.mem_range.mp hk) hb
      _ = _ := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]; ring
  have hlo : μ.real {ω | Blow < Ylo ω} ≤ Real.exp (-ell) :=
    E'.Ylo_probability_bound ℱ hinfo hpath K hell
  have hhi : μ.real {ω | Bhi < Yhi ω} ≤ Real.exp (-ell) :=
    E'.Yhi_probability_bound ℱ hinfo hpath hK hell
  have htotal : μ.real Btotal ≤ 2 * (K : ℝ) *
      ((Fintype.card (S × A) : ℝ) * (K : ℝ) * (H+1) * (1 / budget)) + 2 * Real.exp (-ell) := by
    have hu := (measureReal_union_le Bconf ({ω | Blow < Ylo ω} ∪ {ω | Bhi < Yhi ω})).trans
      (add_le_add hconf (measureReal_union_le {ω | Blow < Ylo ω} {ω | Bhi < Yhi ω}))
    exact hu.trans (by linarith)
  apply le_trans (measureReal_mono ?_ (measure_ne_top μ _)) htotal
  intro ω herr
  by_cases hbc : ω ∈ Bconf
  · exact Or.inl hbc
  by_cases hbl : Blow < Ylo ω
  · exact Or.inr (Or.inl hbl)
  by_cases hbh : Bhi < Yhi ω
  · exact Or.inr (Or.inr hbh)
  have hgood : ∀ k < K, ω ∈ P'.goodKL Λ k := by
    intro k hk
    by_contra hbad
    apply hbc
    exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hk, hbad⟩⟩
  have hrow : ∀ k, k < K → ∀ s a, H+1 ≤ P'.counts ω k (s,a) →
      hellingerSq (E'.latent ω s a) (P'.sampledKernels ω k s a) ≤ 2 * Λ / P'.counts ω k (s,a) := by
    intro k hk s a hn
    exact P'.goodKL_radius hΛ k ω (hgood k hk) (s,a) (by omega)
  have hs := StageCharging.risk_hybrid_sum_bound_stage β hβ c hc
    (P'.policies ω) (E'.latent ω) (P'.sampledKernels ω) s₀ (P'.counts ω) hΛ K H hrow
  have hbnd : Weights.stagew β (H+1) * Ylo ω + 4 * Real.sqrt (Weights.stageWsq β (H+1)) *
      Real.sqrt (Λ * (K : ℝ) * Yhi ω) ≤
      Weights.stagew β (H+1) * Blow + 4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) * Bhi) := by
    exact add_le_add (mul_le_mul_of_nonneg_left (le_of_not_gt hbl) (StageCharging.stagew_nonneg β (H+1)))
      (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
        (mul_le_mul_of_nonneg_left (le_of_not_gt hbh) (by positivity)))
        (show 0 ≤ 4 * Real.sqrt (Weights.stageWsq β (H+1)) from mul_nonneg (by norm_num) (Real.sqrt_nonneg (Weights.stageWsq β (H+1)))))
  have hs' : (∑ k ∈ Finset.range K, P'.stageRiskError β c k ω) ≤
      Weights.stagew β (H+1) * Blow + 4 * Real.sqrt (Weights.stageWsq β (H+1)) * Real.sqrt (Λ * (K : ℝ) * Bhi) :=
    hs.trans hbnd
  exact False.elim (not_lt_of_ge hs' herr)

theorem stage_lemma_5_5
    (external : ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1) {K : ℕ} (hK : 1 ≤ K) :
    (∑ k ∈ Finset.range K, ∫ ω, P'.stageRiskError β c k ω ∂μ) ≤
      Target.confidence (Target.scale (Real.sqrt (Weights.stageWsq β (H+1))) (Fintype.card S) (Fintype.card A))
        (Fintype.card S) (Fintype.card A) (H+1) K * Real.sqrt (K : ℝ) +
      (2 * (Fintype.card S : ℝ) * (Fintype.card A : ℝ) * (H+1) * Weights.stagew β (H+1) + (H+1 : ℝ)/2) := by
  have hs : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty S)
  have ha : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hh : (1 : ℝ) ≤ (H+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hraw := stage_risk_expectation_bound_raw E' P' external β hβ c hc hK
  rw [P'.klThreshold_expected_eq_target K] at hraw
  simp only [Fintype.card_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at hraw
  rw [Bounds.expected_high_eq_confidence hs ha hh K hK] at hraw
  linarith

theorem stage_theorem_5_6
    (external : ExternalCategoricalConcentration (S := S))
    (β : ℕ → ℝ) (hβ : ∀ j, 0 < β j ∧ β j ≤ 1) (c : ℕ → S → A → ℝ)
    (hc : ∀ h s a, 0 ≤ c h s a ∧ c h s a ≤ 1)
    (ℱ : Filtration ℕ ‹MeasurableSpace Ω›)
    (hinfo : ∀ k, MeasurableSpace.comap (E'.info k) inferInstance = ℱ k)
    (hpath : ∀ k, Measurable[ℱ (k+1), inferInstance] (E'.path k))
    {K : ℕ} (hK : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    μ.real {ω | Bounds.certificate (Fintype.card S) (Fintype.card A) (H+1)
      (Real.sqrt (Weights.stageWsq β (H+1))) (Weights.stagew β (H+1)) δ K <
        ∑ k ∈ Finset.range K, P'.stageRiskError β c k ω} ≤ δ := by
  have hs : (1 : ℝ) ≤ Fintype.card S := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty S)
  have ha : (1 : ℝ) ≤ Fintype.card A := by exact_mod_cast Fintype.card_pos_iff.mpr (inferInstance : Nonempty A)
  have hh : (1 : ℝ) ≤ (H+1 : ℝ) := by have := Nat.cast_nonneg (α := ℝ) H; linarith
  let budget := Bounds.certificateBudget (Fintype.card S) (Fintype.card A) (H+1) δ K
  have hb : 1 ≤ budget := Bounds.certificateBudget_one_le hs ha hh hδ hδ1 hK
  have hell : 0 < Bounds.ell δ := Bounds.ell_pos hδ hδ1
  have hraw := stage_risk_certificate_probability_raw E' P' external β hβ c hc ℱ hinfo hpath hK hb hell
  have hcharge := Bounds.certificate_budget_charge (show (0:ℝ)<Fintype.card S by linarith)
    (show (0:ℝ)<Fintype.card A by linarith) (show (0:ℝ)<(H+1:ℝ) by linarith) hδ
    (show 0 < K by omega)
  have hbudget : (Fintype.card (S × A) : ℝ) * (K:ℝ) * (H+1) * (1 / budget) =
      δ / (4 * (K:ℝ)) := by
    convert hcharge using 1 <;> simp only [Fintype.card_prod, Nat.cast_mul, budget] <;> ring
  rw [hbudget, Bounds.exp_neg_ell hδ] at hraw
  have hK0 : (K : ℝ) ≠ 0 := by exact_mod_cast (show K ≠ 0 by omega)
  have hprob : 2 * (K:ℝ) * (δ/(4*(K:ℝ))) + 2*(δ/4) = δ := by field_simp; ring
  rw [hprob] at hraw
  convert hraw using 1
  congr 1
  ext ω
  congr 1
  unfold Bounds.certificate Bounds.certificateLog klThreshold
  simp only [Fintype.card_prod, Nat.cast_mul, Nat.cast_add, Nat.cast_one, budget]
  ring


end StageSourceHorizon
end PosteriorSystem
end
end Paper36.Statistical
