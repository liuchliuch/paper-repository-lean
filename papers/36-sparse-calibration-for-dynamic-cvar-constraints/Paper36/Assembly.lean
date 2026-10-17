import Paper36.BankTarget
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Integrating the pathwise bank inequalities

This is the expectation assembly layer of Theorem 4.2 and Corollary B.1.
All random variables live on an actual probability space and all displayed
expectations are Bochner integrals. The model-error estimates and posterior
symmetry are explicit inputs: this file does not prove Lemmas 5.5 or 5.8.
In particular, an expectation model-error estimate is never used as a pathwise
estimate. The bank and its calibration counter retain Algorithm 1's recurrence.
-/

namespace Paper36.Assembly

open MeasureTheory
open scoped BigOperators

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The bank on a random path, with sampled slack `d n ω` in episode `n`. -/
def bankRV (T : ℕ → ℝ) (d : ℕ → Ω → ℝ) (K : ℕ) (ω : Ω) : ℝ :=
  Bank.bank T (fun n => d n ω) K

/-- The random calibration counter, coerced to a real random variable. -/
def countRV (T : ℕ → ℝ) (d : ℕ → Ω → ℝ) (K : ℕ) (ω : Ω) : ℝ :=
  (Bank.count T (fun n => d n ω) K : ℝ)

/-- Zero target makes the random bank identically zero, as in the H=1 endpoint. -/
theorem zero_target_bank (d : ℕ → Ω → ℝ) (K : ℕ) :
    bankRV (fun _ => 0) d K = fun _ => 0 := by
  funext ω
  exact (Bank.zero_target (fun n => d n ω) K).1

/-- Zero target makes the random calibration counter identically zero. -/
theorem zero_target_count (d : ℕ → Ω → ℝ) (K : ℕ) :
    countRV (fun _ => 0) d K = fun _ => 0 := by
  funext ω
  unfold countRV
  rw [(Bank.zero_target (fun n => d n ω) K).2]
  norm_num

/-- The almost-sure support-gap bounds (5.15) for actual calibration deposits. -/
def DepositBounds (T : ℕ → ℝ) (d : ℕ → Ω → ℝ) (Δ τ : ℝ) (ω : Ω) : Prop :=
  ∀ n, Bank.calibrates T (fun j => d j ω) n → Δ ≤ d (n + 1) ω ∧ d (n + 1) ω ≤ τ

/-- Episode totals, with episode `n + 1` represented by index `n`. -/
def total (f : ℕ → Ω → ℝ) (K : ℕ) (ω : Ω) : ℝ :=
  ∑ n ∈ Finset.range K, f n ω

theorem measurable_bank (T : ℕ → ℝ) (d : ℕ → Ω → ℝ)
    (hd : ∀ n, Measurable (d n)) (K : ℕ) : Measurable (bankRV T d K) := by
  induction K with
  | zero => exact measurable_const
  | succ K ih =>
      change Measurable (fun ω => if bankRV T d K ω < T (K + 1)
        then bankRV T d K ω + d (K + 1) ω else bankRV T d K ω)
      exact Measurable.ite (measurableSet_lt ih measurable_const)
        (ih.add (hd (K + 1))) ih

theorem measurable_count (T : ℕ → ℝ) (d : ℕ → Ω → ℝ)
    (hd : ∀ n, Measurable (d n)) (K : ℕ) : Measurable (countRV T d K) := by
  induction K with
  | zero =>
      have heq : countRV T d 0 = fun _ : Ω => (0 : ℝ) := by
        funext ω
        simp [countRV]
      rw [heq]
      exact measurable_const
  | succ K ih =>
      have heq : countRV T d (K + 1) = fun ω => countRV T d K ω +
          if bankRV T d K ω < T (K + 1) then 1 else 0 := by
        funext ω
        simp only [countRV, Bank.count, Bank.calibrates, bankRV]
        split_ifs <;> simp
      rw [heq]
      exact ih.add (Measurable.ite
        (measurableSet_lt (measurable_bank T d hd K) measurable_const)
        measurable_const measurable_const)

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

omit [IsProbabilityMeasure μ] in
theorem integrable_total (f : ℕ → Ω → ℝ) (hf : ∀ n, Integrable (f n) μ) (K : ℕ) :
    Integrable (total f K) μ :=
  integrable_finset_sum _ (fun n _ => hf n)

/-- Integrability of the counter follows from its actual bound by `K`. -/
theorem integrable_count (T : ℕ → ℝ) (d : ℕ → Ω → ℝ)
    (hd : ∀ n, Measurable (d n)) (K : ℕ) : Integrable (countRV T d K) μ := by
  apply Integrable.of_bound (measurable_count T d hd K).aestronglyMeasurable (K : ℝ)
  exact ae_of_all μ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Nat.cast_nonneg _)]
    change (Bank.count T (fun n => d n ω) K : ℝ) ≤ (K : ℝ)
    exact_mod_cast Bank.count_le T (fun n => d n ω) K)

/-- Integrability of the bank is proved from the true recurrence and bounded deposits. -/
theorem integrable_bank (T : ℕ → ℝ) (d : ℕ → Ω → ℝ) (Δ τ : ℝ)
    (hd : ∀ n, Measurable (d n)) (hΔ : 0 ≤ Δ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds T d Δ τ ω) (K : ℕ) :
    Integrable (bankRV T d K) μ := by
  apply Integrable.of_bound (measurable_bank T d hd K).aestronglyMeasurable |T K + τ|
  filter_upwards [hdeposit] with ω hω
  have hlo := Bank.bank_nonneg T (fun n => d n ω)
    (fun n hn => hΔ.trans (hω n hn).1) K
  have hhi := Bank.bank_le_target_add T (fun n => d n ω) τ hT hbase
    (fun n hn => (hω n hn).2) K
  change ‖Bank.bank T (fun n => d n ω) K‖ ≤ |T K + τ|
  rw [Real.norm_eq_abs, abs_of_nonneg hlo]
  exact hhi.trans (le_abs_self _)

/-- The expected calibration count inherits the full minimum in (4.12). -/
theorem expected_count_bound (T : ℕ → ℝ) (d : ℕ → Ω → ℝ) (Δ τ : ℝ)
    (hd : ∀ n, Measurable (d n)) (hΔ : 0 < Δ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds T d Δ τ ω) (K : ℕ) :
    (∫ ω, countRV T d K ω ∂μ) ≤ min (K : ℝ) ((T K + τ) / Δ) := by
  have hle : countRV T d K ≤ᵐ[μ] fun _ => min (K : ℝ) ((T K + τ) / Δ) := by
    filter_upwards [hdeposit] with ω hω
    exact Bank.calibration_count_bound T (fun n => d n ω) Δ τ hΔ hT hbase
      (fun n hn => (hω n hn).1) (fun n hn => (hω n hn).2) K
  simpa using integral_mono_ae (integrable_count T d hd K) (integrable_const _) hle

/-- The uniform pathwise deficit becomes an actual expected deficit inequality. -/
theorem expected_deficit_bound (T : ℕ → ℝ) (d : ℕ → Ω → ℝ) (Δ τ R : ℝ)
    (hd : ∀ n, Measurable (d n)) (hΔ : 0 < Δ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ) (hzero : T 0 = 0)
    (hsub : ∀ j n, T (j + n) ≤ T j + T n)
    (henv : ∀ n, T n - (n : ℝ) * Δ ≤ R)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds T d Δ τ ω) (K : ℕ) :
    T K - (∫ ω, bankRV T d K ω ∂μ) ≤ R := by
  have hbi := integrable_bank T d Δ τ hd hΔ.le hT hbase hdeposit K
  have hle : (fun ω => T K - bankRV T d K ω) ≤ᵐ[μ] fun _ => R := by
    filter_upwards [hdeposit] with ω hω
    exact Bank.deficit_le_residual T (fun n => d n ω) Δ R hzero
      (fun n hn => (hω n hn).1) hsub henv K
  have hi := integral_mono_ae ((integrable_const (T K)).sub hbi) (integrable_const R) hle
  change (∫ ω, T K - bankRV T d K ω ∂μ) ≤ (∫ _ω : Ω, R ∂μ) at hi
  rw [integral_sub (integrable_const (T K)) hbi] at hi
  simpa using hi

/-- The actual expected risk decomposition, including certified feasibility errors. -/
theorem expected_risk_decomposition (T : ℕ → ℝ) (d risk sampled : ℕ → Ω → ℝ)
    (ε : ℕ → ℝ) (τ : ℝ) (K : ℕ)
    (hbi : Integrable (bankRV T d K) μ)
    (hrisk : ∀ n, Integrable (risk n) μ) (hsampled : ∀ n, Integrable (sampled n) μ)
    (hε : ∀ n, 0 ≤ ε n)
    (horacle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates T (fun j => d j ω) n → sampled n ω = τ - d (n + 1) ω) ∧
      (¬Bank.calibrates T (fun j => d j ω) n → sampled n ω ≤ τ + ε n)) :
    (∫ ω, total (fun n ω => risk n ω - τ) K ω ∂μ) ≤
      (∫ ω, total (fun n ω => risk n ω - sampled n ω) K ω ∂μ) +
      (∑ n ∈ Finset.range K, ε n) - (∫ ω, bankRV T d K ω ∂μ) := by
  have hri := integrable_total (fun n ω => risk n ω - τ)
    (fun n => (hrisk n).sub (integrable_const τ)) K
  have hmi := integrable_total (fun n ω => risk n ω - sampled n ω)
    (fun n => (hrisk n).sub (hsampled n)) K
  have hle : total (fun n ω => risk n ω - τ) K ≤ᵐ[μ]
      fun ω => total (fun n ω => risk n ω - sampled n ω) K ω +
        (∑ n ∈ Finset.range K, ε n) - bankRV T d K ω := by
    filter_upwards [horacle] with ω hω
    exact Bank.risk_decomposition_bound T (fun n => d n ω)
      (fun n => risk n ω) (fun n => sampled n ω) ε τ hε
      (fun n hn => (hω n).1 hn) (fun n hn => (hω n).2 hn) K
  have hi := integral_mono_ae hri ((hmi.add (integrable_const _)).sub hbi) hle
  change (∫ ω, total (fun n ω => risk n ω - τ) K ω ∂μ) ≤
    (∫ ω, (total (fun n ω => risk n ω - sampled n ω) K ω +
      (∑ n ∈ Finset.range K, ε n)) - bankRV T d K ω ∂μ) at hi
  have hsub := integral_sub (hmi.add (integrable_const (∑ n ∈ Finset.range K, ε n))) hbi
  simp only [Pi.add_apply] at hsub
  rw [hsub] at hi
  have hadd := integral_add hmi (integrable_const (∑ n ∈ Finset.range K, ε n))
  rw [hadd] at hi
  simpa using hi

/-- The risk half of Theorem 4.2's assembly. The simulation bound is an
expectation hypothesis; no pathwise model-error premise occurs. -/
theorem conditional_expected_risk_bound (T : ℕ → ℝ) (d risk sampled : ℕ → Ω → ℝ)
    (ε : ℕ → ℝ) (τ Δ D R C : ℝ) (K : ℕ)
    (hd : ∀ n, Measurable (d n)) (hΔ : 0 < Δ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ) (hzero : T 0 = 0)
    (hsub : ∀ j n, T (j + n) ≤ T j + T n)
    (henv : ∀ n, T n - (n : ℝ) * Δ ≤ R)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds T d Δ τ ω)
    (hrisk : ∀ n, Integrable (risk n) μ) (hsampled : ∀ n, Integrable (sampled n) μ)
    (hε : ∀ n, 0 ≤ ε n)
    (horacle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates T (fun j => d j ω) n → sampled n ω = τ - d (n + 1) ω) ∧
      (¬Bank.calibrates T (fun j => d j ω) n → sampled n ω ≤ τ + ε n))
    (hmodel : (∫ ω, total (fun n ω => risk n ω - sampled n ω) K ω ∂μ) ≤ C + D)
    (hdom : C ≤ T K) :
    (∫ ω, total (fun n ω => risk n ω - τ) K ω ∂μ) ≤
      D + R + ∑ n ∈ Finset.range K, ε n := by
  have hb := integrable_bank T d Δ τ hd hΔ.le hT hbase hdeposit K
  have hdec := expected_risk_decomposition T d risk sampled ε τ K hb
    hrisk hsampled hε horacle
  have hdef := expected_deficit_bound T d Δ τ R hd hΔ hT hbase hzero
    hsub henv hdeposit K
  linarith

/-- Integrating the oracle loss uses the random calibration count, rather than
replacing that count by a deterministic quantity before taking expectations. -/
theorem expected_sampled_reward_shortfall (T : ℕ → ℝ)
    (d loss : ℕ → Ω → ℝ) (ζ : ℕ → ℝ) (H : ℝ) (K : ℕ)
    (hd : ∀ n, Measurable (d n)) (hloss : ∀ n, Integrable (loss n) μ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (horacle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates T (fun j => d j ω) n → loss n ω ≤ H) ∧
      (¬Bank.calibrates T (fun j => d j ω) n → loss n ω ≤ ζ n)) :
    (∫ ω, total loss K ω ∂μ) ≤
      H * (∫ ω, countRV T d K ω ∂μ) + ∑ n ∈ Finset.range K, ζ n := by
  have hci := integrable_count (μ := μ) T d hd K
  have hle : total loss K ≤ᵐ[μ]
      fun ω => H * countRV T d K ω + ∑ n ∈ Finset.range K, ζ n := by
    filter_upwards [horacle] with ω hω
    exact Bank.sampled_reward_shortfall T (fun n => d n ω) (fun n => loss n ω)
      ζ H hζ (fun n hn => (hω n).1 hn) (fun n hn => (hω n).2 hn) K
  have hi := integral_mono_ae (integrable_total loss hloss K)
    ((hci.const_mul H).add (integrable_const _)) hle
  change (∫ ω, total loss K ω ∂μ) ≤
    (∫ ω, H * countRV T d K ω + (∑ n ∈ Finset.range K, ζ n) ∂μ) at hi
  rw [integral_add (hci.const_mul H) (integrable_const _), integral_const_mul] at hi
  simpa using hi

omit [IsProbabilityMeasure μ] in
/-- Per-episode posterior matching of expectations gives the total symmetry
identity (5.18), using finite-sum and subtraction laws for actual integrals. -/
theorem total_symmetry_from_matching_expectations
    (opt sampledOpt : ℕ → Ω → ℝ)
    (hopt : ∀ n, Integrable (opt n) μ) (hsopt : ∀ n, Integrable (sampledOpt n) μ)
    (hmatch : ∀ n, (∫ ω, opt n ω ∂μ) = (∫ ω, sampledOpt n ω ∂μ)) (K : ℕ) :
    (∫ ω, total (fun n ω => opt n ω - sampledOpt n ω) K ω ∂μ) = 0 := by
  change (∫ ω, ∑ n ∈ Finset.range K, (opt n ω - sampledOpt n ω) ∂μ) = 0
  have hsum := integral_finset_sum (Finset.range K) (fun n _ => (hopt n).sub (hsopt n))
  simp only [Pi.sub_apply] at hsum
  rw [hsum]
  apply Finset.sum_eq_zero
  intro n hn
  rw [integral_sub (hopt n) (hsopt n), hmatch n, sub_self]

/-- The reward half of the main theorem, with the posterior-symmetry identity
and Lemma 5.8's expected model error kept as explicit probabilistic inputs. -/
theorem conditional_expected_reward_bound (T : ℕ → ℝ)
    (d opt sampledOpt reward sampledReward : ℕ → Ω → ℝ) (ζ : ℕ → ℝ)
    (H Δ τ Q : ℝ) (K : ℕ)
    (hd : ∀ n, Measurable (d n)) (hH : 0 ≤ H) (hΔ : 0 < Δ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds T d Δ τ ω)
    (hopt : ∀ n, Integrable (opt n) μ) (hsopt : ∀ n, Integrable (sampledOpt n) μ)
    (hr : ∀ n, Integrable (reward n) μ) (hsr : ∀ n, Integrable (sampledReward n) μ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (horacle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates T (fun j => d j ω) n → sampledOpt n ω - sampledReward n ω ≤ H) ∧
      (¬Bank.calibrates T (fun j => d j ω) n → sampledOpt n ω - sampledReward n ω ≤ ζ n))
    (hsym : (∫ ω, total (fun n ω => opt n ω - sampledOpt n ω) K ω ∂μ) = 0)
    (hmodel : (∫ ω, total (fun n ω => sampledReward n ω - reward n ω) K ω ∂μ) ≤ Q) :
    (∫ ω, total (fun n ω => opt n ω - reward n ω) K ω ∂μ) ≤
      Q + H * ((T K + τ) / Δ) + ∑ n ∈ Finset.range K, ζ n := by
  have hsi := integrable_total (fun n ω => opt n ω - sampledOpt n ω)
    (fun n => (hopt n).sub (hsopt n)) K
  have hli := integrable_total (fun n ω => sampledOpt n ω - sampledReward n ω)
    (fun n => (hsopt n).sub (hsr n)) K
  have hmi := integrable_total (fun n ω => sampledReward n ω - reward n ω)
    (fun n => (hsr n).sub (hr n)) K
  have heq : total (fun n ω => opt n ω - reward n ω) K =
      fun ω => total (fun n ω => opt n ω - sampledOpt n ω) K ω +
        total (fun n ω => sampledOpt n ω - sampledReward n ω) K ω +
        total (fun n ω => sampledReward n ω - reward n ω) K ω := by
    funext ω
    simp only [total, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  have hdec : (∫ ω, total (fun n ω => opt n ω - reward n ω) K ω ∂μ) =
      (∫ ω, total (fun n ω => sampledOpt n ω - sampledReward n ω) K ω ∂μ) +
      (∫ ω, total (fun n ω => sampledReward n ω - reward n ω) K ω ∂μ) := by
    rw [heq]
    change (∫ ω, (total (fun n ω => opt n ω - sampledOpt n ω) K ω +
      total (fun n ω => sampledOpt n ω - sampledReward n ω) K ω) +
      total (fun n ω => sampledReward n ω - reward n ω) K ω ∂μ) = _
    have houter := integral_add (hsi.add hli) hmi
    simp only [Pi.add_apply] at houter
    rw [houter]
    have hadd := integral_add hsi hli
    rw [hadd, hsym, zero_add]
  have hl := expected_sampled_reward_shortfall T d
    (fun n ω => sampledOpt n ω - sampledReward n ω) ζ H K hd
    (fun n => (hsopt n).sub (hsr n)) hζ horacle
  have hc := (expected_count_bound T d Δ τ hd hΔ hT hbase hdeposit K).trans
    (min_le_right _ _)
  have hm := mul_le_mul_of_nonneg_left hc hH
  rw [hdec]
  linarith

omit [IsProbabilityMeasure μ] in
/-- Simultaneous almost-sure sparsity for the actual source target. -/
theorem calibration_sparse_ae_actual {s a h w Δ τ : ℝ} (d : ℕ → Ω → ℝ)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ)
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds (BankTarget.paperTarget s a h w) d Δ τ ω) :
    ∀ᵐ ω ∂μ, Filter.Tendsto
      (fun K : ℕ => countRV (BankTarget.paperTarget s a h w) d K ω / (K : ℝ))
      Filter.atTop (nhds 0) := by
  filter_upwards [hdeposit] with ω hω
  exact BankTarget.calibration_sparse (fun n => d n ω) hs ha hh hw hΔ hτ hω

/-- Conditional assembly of the main theorem with the actual target and explicit R_*.

`hmodelRisk` is precisely the expectation estimate to be supplied by Lemma 5.5,
`hmodelReward` is the expectation estimate to be supplied by Lemma 5.8, and
`hsym` is posterior symmetry (5.18). None is proved or silently assumed to hold
pathwise here. Setting both certified error sequences to zero gives the exact
oracle case; retaining them gives Corollary B.1's additive errors.
-/
theorem conditional_main_bounds {s a h w Δ τ D Q : ℝ}
    (d risk sampledRisk opt sampledOpt reward sampledReward : ℕ → Ω → ℝ)
    (ε ζ : ℕ → ℝ) (K : ℕ) (hk : 1 ≤ K)
    (hs : 1 ≤ s) (ha : 1 ≤ a) (hh : 1 ≤ h) (hw : 0 ≤ w)
    (hΔ : 0 < Δ) (hτ : 0 ≤ τ) (hd : ∀ n, Measurable (d n))
    (hdeposit : ∀ᵐ ω ∂μ, DepositBounds (BankTarget.paperTarget s a h w) d Δ τ ω)
    (hrisk : ∀ n, Integrable (risk n) μ) (hsrisk : ∀ n, Integrable (sampledRisk n) μ)
    (hopt : ∀ n, Integrable (opt n) μ) (hsopt : ∀ n, Integrable (sampledOpt n) μ)
    (hr : ∀ n, Integrable (reward n) μ) (hsr : ∀ n, Integrable (sampledReward n) μ)
    (hε : ∀ n, 0 ≤ ε n) (hζ : ∀ n, 0 ≤ ζ n)
    (hriskOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledRisk n ω = τ - d (n + 1) ω) ∧
      (¬Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledRisk n ω ≤ τ + ε n))
    (hrewardOracle : ∀ᵐ ω ∂μ, ∀ n,
      (Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledOpt n ω - sampledReward n ω ≤ h) ∧
      (¬Bank.calibrates (BankTarget.paperTarget s a h w) (fun j => d j ω) n →
        sampledOpt n ω - sampledReward n ω ≤ ζ n))
    (hmodelRisk : (∫ ω, total (fun n ω => risk n ω - sampledRisk n ω) K ω ∂μ) ≤
      Target.confidence (Target.scale w s a) s a h K * Real.sqrt (K : ℝ) + D)
    (hmodelReward : (∫ ω, total (fun n ω => sampledReward n ω - reward n ω) K ω ∂μ) ≤ Q)
    (hsym : (∫ ω, total (fun n ω => opt n ω - sampledOpt n ω) K ω ∂μ) = 0) :
    ((∫ ω, total (fun n ω => risk n ω - τ) K ω ∂μ) ≤
      D + BankTarget.paperResidual s a h w Δ + ∑ n ∈ Finset.range K, ε n) ∧
    ((∫ ω, total (fun n ω => opt n ω - reward n ω) K ω ∂μ) ≤
      Q + h * ((BankTarget.paperTarget s a h w K + τ) / Δ) +
        ∑ n ∈ Finset.range K, ζ n) ∧
    ((∫ ω, countRV (BankTarget.paperTarget s a h w) d K ω ∂μ) ≤
      min (K : ℝ) ((BankTarget.paperTarget s a h w K + τ) / Δ)) := by
  have hp := BankTarget.actual_target_properties hs ha hh hw hΔ
  have hbase : 0 ≤ BankTarget.paperTarget s a h w 0 + τ := by
    rw [hp.2.1]
    simpa using hτ
  refine ⟨?_, ?_, ?_⟩
  · exact conditional_expected_risk_bound _ d risk sampledRisk ε τ Δ D _ _ K hd hΔ
      hp.1 hbase hp.2.1 hp.2.2.1 hp.2.2.2.1 hdeposit hrisk hsrisk hε hriskOracle
      hmodelRisk (Target.confidence_majorization (Target.scale_nonneg hw) hs ha hh hk)
  · exact conditional_expected_reward_bound _ d opt sampledOpt reward sampledReward ζ
      h Δ τ Q K hd (by linarith) hΔ hp.1 hbase hdeposit
      hopt hsopt hr hsr hζ hrewardOracle hsym hmodelReward
  · exact expected_count_bound _ d Δ τ hd hΔ hp.1 hbase hdeposit K

end
end Paper36.Assembly
