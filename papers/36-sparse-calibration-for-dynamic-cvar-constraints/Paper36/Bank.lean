import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Tactic.NormNum

/-!
# The deterministic risk bank of Paper 36

The episode index in `calibrates T d n` is zero based: it means that paper episode
`n + 1` calibrates. `d (n + 1)` is its exact sampled-model slack. These definitions
contain the actual Algorithm 1 threshold rule; none of the bank conclusions are
fields of an assumed invariant. Probability and the specific analytic target are
separate inputs to the deterministic consequences proved below.
-/
namespace Paper36.Bank

noncomputable section

/-- Algorithm 1: only a calibration episode makes a deposit. -/
def bank (T d : ℕ → ℝ) : ℕ → ℝ
  | 0 => 0
  | n + 1 => if bank T d n < T (n + 1) then bank T d n + d (n + 1)
      else bank T d n

/-- Episode `n + 1` uses the minimum-risk calibration policy. -/
def calibrates (T d : ℕ → ℝ) (n : ℕ) : Prop := bank T d n < T (n + 1)

instance (T d : ℕ → ℝ) (n : ℕ) : Decidable (calibrates T d n) :=
  inferInstanceAs (Decidable (bank T d n < T (n + 1)))

/-- Number of calibration episodes among the first `K` episodes. -/
def count (T d : ℕ → ℝ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => count T d n + if calibrates T d n then 1 else 0

/-- The slack actually credited by the bank at episode `n + 1`. -/
def credit (T d : ℕ → ℝ) (n : ℕ) : ℝ :=
  if calibrates T d n then d (n + 1) else 0

@[simp] theorem bank_zero (T d : ℕ → ℝ) : bank T d 0 = 0 := rfl
@[simp] theorem count_zero (T d : ℕ → ℝ) : count T d 0 = 0 := rfl

theorem bank_step (T d : ℕ → ℝ) (n : ℕ) :
    bank T d (n + 1) = bank T d n + credit T d n := by
  simp only [bank, credit, calibrates]
  split_ifs <;> simp

/-- Nonnegative calibration deposits make the bank nonnegative on every path. -/
theorem bank_nonneg (T d : ℕ → ℝ)
    (hd : ∀ n, calibrates T d n → 0 ≤ d (n + 1)) (K : ℕ) :
    0 ≤ bank T d K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [bank_step]
      simp only [credit]
      split_ifs with h
      · exact add_nonneg ih (hd K h)
      · simpa using ih

/-- Deposits never withdraw credit. -/
theorem bank_monotone (T d : ℕ → ℝ)
    (hd : ∀ n, calibrates T d n → 0 ≤ d (n + 1)) : Monotone (bank T d) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [bank_step]
  have hc : 0 ≤ credit T d n := by
    unfold credit
    split_ifs with h
    · exact hd n h
    · exact le_rfl
  linarith

/-- The bank is exactly the sum of calibration deposits (exploitation slack is ignored). -/
theorem bank_eq_sum_credit (T d : ℕ → ℝ) (K : ℕ) :
    bank T d K = ∑ n ∈ Finset.range K, credit T d n := by
  induction K with
  | zero => simp
  | succ K ih => rw [bank_step, Finset.sum_range_succ, ih]

/-- The recursive counter equals the number of episodes selected by the threshold rule. -/
theorem count_eq_sum (T d : ℕ → ℝ) (K : ℕ) :
    count T d K = ∑ n ∈ Finset.range K, if calibrates T d n then 1 else 0 := by
  induction K with
  | zero => simp
  | succ K ih => rw [count, Finset.sum_range_succ, ih]

theorem count_le (T d : ℕ → ℝ) (K : ℕ) : count T d K ≤ K := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp only [count]
      split_ifs <;> omega

/-- Equation (5.15) implies the count times the uniform gap is covered by the bank. -/
theorem count_mul_gap_le_bank (T d : ℕ → ℝ) (Δ : ℝ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1)) (K : ℕ) :
    (count T d K : ℝ) * Δ ≤ bank T d K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [bank_step]
      simp only [count, credit]
      split_ifs with h
      · have hd := hgap K h
        push_cast
        nlinarith
      · simpa using ih

/-- Every bank value is below the current target plus one maximal deposit. -/
theorem bank_le_target_add (T d : ℕ → ℝ) (τ : ℝ)
    (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ) (K : ℕ) :
    bank T d K ≤ T K + τ := by
  induction K with
  | zero => simpa using hbase
  | succ K ih =>
      rw [bank_step]
      simp only [credit]
      split_ifs with h
      · have hb : bank T d K < T (K + 1) := h
        have hd := hcap K h
        linarith
      · have ht := hT (Nat.le_succ K)
        linarith

/-- The strict last-calibration estimate used immediately before (4.12). -/
theorem bank_lt_target_add_of_count_pos (T d : ℕ → ℝ) (τ : ℝ)
    (hT : Monotone T)
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ) (K : ℕ)
    (hpos : 0 < count T d K) : bank T d K < T K + τ := by
  induction K with
  | zero => simp at hpos
  | succ K ih =>
      rw [bank_step]
      simp only [credit]
      split_ifs with h
      · have hb : bank T d K < T (K + 1) := h
        have hd := hcap K h
        linarith
      · have hp : 0 < count T d K := by simpa [count, h] using hpos
        have hb := ih hp
        have ht := hT (Nat.le_succ K)
        linarith

/-- Equation (4.12), with the two sides of the minimum given separately. -/
theorem calibration_count_bound (T d : ℕ → ℝ) (Δ τ : ℝ)
    (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ) (K : ℕ) :
    (count T d K : ℝ) ≤ min (K : ℝ) ((T K + τ) / Δ) := by
  apply le_min
  · exact_mod_cast count_le T d K
  · apply (le_div_iff₀ hΔ).2
    exact (count_mul_gap_le_bank T d Δ hgap K).trans
      (bank_le_target_add T d τ hT hbase hcap K)

/-- A trailing calibration block has an anchor at the last exploitation episode.
`n = 0` covers current exploitation; `n = K` covers calibration from the start. -/
theorem trailing_anchor (T d : ℕ → ℝ) (Δ : ℝ) (hzero : T 0 = 0)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1)) (K : ℕ) :
    ∃ n ≤ K, T (K - n) + (n : ℝ) * Δ ≤ bank T d K := by
  induction K with
  | zero => exact ⟨0, by omega, by simp [hzero]⟩
  | succ K ih =>
      rw [bank_step]
      simp only [credit]
      split_ifs with h
      · obtain ⟨n, hn, hb⟩ := ih
        refine ⟨n + 1, by omega, ?_⟩
        rw [Nat.add_sub_add_right]
        have hd := hgap K h
        push_cast
        nlinarith
      · refine ⟨0, Nat.zero_le _, ?_⟩
        have hb : T (K + 1) ≤ bank T d K := le_of_not_gt h
        simpa using hb

/-- The pathwise cancellation in (5.17), derived from the actual bank recurrence.
The target's subadditivity and its residual envelope are analytic inputs. -/
theorem deficit_le_residual (T d : ℕ → ℝ) (Δ R : ℝ) (hzero : T 0 = 0)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hsub : ∀ j n, T (j + n) ≤ T j + T n)
    (henv : ∀ n, T n - (n : ℝ) * Δ ≤ R) (K : ℕ) :
    T K - bank T d K ≤ R := by
  obtain ⟨n, hn, hb⟩ := trailing_anchor T d Δ hzero hgap K
  have ht := hsub (K - n) n
  rw [Nat.sub_add_cancel hn] at ht
  have hr := henv n
  linarith

/-- When the target is zero, the algorithm never calibrates. This is the bank
part of the `H = 1` endpoint. -/
theorem zero_target (d : ℕ → ℝ) (K : ℕ) :
    bank (fun _ => 0) d K = 0 ∧ count (fun _ => 0) d K = 0 := by
  induction K with
  | zero => simp
  | succ K ih =>
      rcases ih with ⟨hb, hc⟩
      simp [bank, count, calibrates, hb, hc]

/-- Approximate exploitation leaves at most its certified error after bank cancellation. -/
theorem sampled_debt_cancellation (T d debt ε : ℕ → ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hcal : ∀ n, calibrates T d n → debt n = -d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → debt n ≤ ε n) (K : ℕ) :
    (∑ n ∈ Finset.range K, debt n) ≤
      (∑ n ∈ Finset.range K, ε n) - bank T d K := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, bank_step]
      simp only [credit]
      split_ifs with h
      · have hd := hcal K h
        have he := hε K
        linarith
      · have hd := hexp K h
        linarith

/-- Exact-oracle specialization of the sampled-model debt cancellation in (5.16). -/
theorem exact_sampled_debt_cancellation (T d debt : ℕ → ℝ)
    (hcal : ∀ n, calibrates T d n → debt n = -d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → debt n ≤ 0) (K : ℕ) :
    (∑ n ∈ Finset.range K, debt n) ≤ -bank T d K := by
  simpa using sampled_debt_cancellation T d debt (fun _ => 0)
    (fun _ => le_rfl) hcal hexp K

/-- The reward cost of calibration is at most `H` per calibration; certified
optimization error accumulates only additively (the algebra of Corollary B.1). -/
theorem sampled_reward_shortfall (T d loss ζ : ℕ → ℝ) (H : ℝ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (hcal : ∀ n, calibrates T d n → loss n ≤ H)
    (hexp : ∀ n, ¬calibrates T d n → loss n ≤ ζ n) (K : ℕ) :
    (∑ n ∈ Finset.range K, loss n) ≤
      H * (count T d K : ℝ) + ∑ n ∈ Finset.range K, ζ n := by
  induction K with
  | zero => simp
  | succ K ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [count]
      split_ifs with h
      · have hl := hcal K h
        have he := hζ K
        push_cast
        nlinarith
      · have hl := hexp K h
        simpa using (by linarith :
          (∑ n ∈ Finset.range K, loss n) + loss K ≤
          H * (count T d K : ℝ) + ((∑ n ∈ Finset.range K, ζ n) + ζ K))

/-- Risk decomposition and the bank recurrence give the pathwise algebraic
certificate. A separate simulation theorem must supply the model-error bound. -/
theorem risk_decomposition_bound (T d risk sampled ε : ℕ → ℝ) (τ : ℝ)
    (hε : ∀ n, 0 ≤ ε n)
    (hcal : ∀ n, calibrates T d n → sampled n = τ - d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → sampled n ≤ τ + ε n) (K : ℕ) :
    (∑ n ∈ Finset.range K, (risk n - τ)) ≤
      (∑ n ∈ Finset.range K, (risk n - sampled n)) +
      (∑ n ∈ Finset.range K, ε n) - bank T d K := by
  have hb := sampled_debt_cancellation T d (fun n => sampled n - τ) ε hε
    (fun n hn => by change sampled n - τ = -d (n + 1); rw [hcal n hn]; ring)
    (fun n hn => by have := hexp n hn; linarith) K
  have heq : (∑ n ∈ Finset.range K, (risk n - τ)) =
      (∑ n ∈ Finset.range K, (risk n - sampled n)) +
      (∑ n ∈ Finset.range K, (sampled n - τ)) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [heq]
  linarith

/-- Combining a model-error envelope with (5.17) yields the deterministic part
of the uniform risk bound, including the exact additive feasibility-error term. -/
theorem risk_bound_from_model_envelope (T d risk sampled ε : ℕ → ℝ)
    (τ Δ D R : ℝ) (hzero : T 0 = 0)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hsub : ∀ j n, T (j + n) ≤ T j + T n)
    (henv : ∀ n, T n - (n : ℝ) * Δ ≤ R)
    (hε : ∀ n, 0 ≤ ε n)
    (hcal : ∀ n, calibrates T d n → sampled n = τ - d (n + 1))
    (hexp : ∀ n, ¬calibrates T d n → sampled n ≤ τ + ε n) (K : ℕ)
    (hmodel : (∑ n ∈ Finset.range K, (risk n - sampled n)) ≤ T K + D) :
    (∑ n ∈ Finset.range K, (risk n - τ)) ≤
      D + R + ∑ n ∈ Finset.range K, ε n := by
  have hb := risk_decomposition_bound T d risk sampled ε τ hε hcal hexp K
  have hr := deficit_le_residual T d Δ R hzero hgap hsub henv K
  linarith

/-- The reward consequence of the actual calibration-count estimate. This is
(4.10)'s bank contribution; a reward simulation theorem supplies the other term. -/
theorem reward_bound_from_count (T d loss ζ : ℕ → ℝ) (H Δ τ : ℝ)
    (hH : 0 ≤ H) (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ)
    (hζ : ∀ n, 0 ≤ ζ n)
    (hcal : ∀ n, calibrates T d n → loss n ≤ H)
    (hexp : ∀ n, ¬calibrates T d n → loss n ≤ ζ n) (K : ℕ) :
    (∑ n ∈ Finset.range K, loss n) ≤
      H * ((T K + τ) / Δ) + ∑ n ∈ Finset.range K, ζ n := by
  have hl := sampled_reward_shortfall T d loss ζ H hζ hcal hexp K
  have hc := (calibration_count_bound T d Δ τ hΔ hT hbase hgap hcap K).trans
    (min_le_right _ _)
  have hm := mul_le_mul_of_nonneg_left hc hH
  linarith

/-- Bounded costs turn strict feasibility into exactly the deposit bounds (5.15). -/
theorem slack_bounds (τ Δ g : ℝ) (hg : 0 ≤ g) (hgap : g ≤ τ - Δ) :
    Δ ≤ τ - g ∧ τ - g ≤ τ := by constructor <;> linarith

/-- Equality with the target selects exploitation, including the zero-target endpoint. -/
theorem at_target_exploits (T d : ℕ → ℝ) (n : ℕ)
    (heq : bank T d n = T (n + 1)) :
    bank T d (n + 1) = bank T d n ∧ count T d (n + 1) = count T d n := by
  have hn : ¬calibrates T d n := by simp [calibrates, heq]
  simp [bank_step, credit, count, hn]

/-- If the analytic target is sublinear, the actual calibration frequency tends
to zero. The target's logarithmic estimate is intentionally a separate theorem. -/
theorem calibration_sparse_of_target_sublinear (T d : ℕ → ℝ) (Δ τ : ℝ)
    (hΔ : 0 < Δ) (hT : Monotone T) (hbase : 0 ≤ T 0 + τ)
    (hgap : ∀ n, calibrates T d n → Δ ≤ d (n + 1))
    (hcap : ∀ n, calibrates T d n → d (n + 1) ≤ τ)
    (hsmall : Filter.Tendsto (fun K : ℕ => T K / (K : ℝ))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun K : ℕ => (count T d K : ℝ) / (K : ℝ))
      Filter.atTop (nhds 0) := by
  have hτ : Filter.Tendsto (fun K : ℕ => τ / (K : ℝ))
      Filter.atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul tendsto_inverse_atTop_nhds_zero_nat
  have hbound : Filter.Tendsto (fun K : ℕ =>
      (T K / (K : ℝ) + τ / (K : ℝ)) / Δ) Filter.atTop (nhds 0) := by
    simpa using (hsmall.add hτ).div_const Δ
  apply squeeze_zero (fun K => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (fun K => ?_) hbound
  have hc := (calibration_count_bound T d Δ τ hΔ hT hbase hgap hcap K).trans
    (min_le_right _ _)
  have hn : 0 ≤ (K : ℝ) := Nat.cast_nonneg _
  have hh := div_le_div_of_nonneg_right hc hn
  calc
    (count T d K : ℝ) / (K : ℝ) ≤ ((T K + τ) / Δ) / (K : ℝ) := hh
    _ = (T K / (K : ℝ) + τ / (K : ℝ)) / Δ := by ring

end
end Paper36.Bank
