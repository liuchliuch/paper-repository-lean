import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Nat.Log
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import CalibrationDistance.Grid
import CalibrationDistance.Optimization

/-!
# Dyadic restarts

The geometric calculation in (7.2) and the causal restart construction used in
Corollary 2.2. Round numbers in this file are zero based: epoch `k` begins at
round `2^k - 1` and has `2^k` rounds.
-/

namespace CalibrationDistance

noncomputable section

open scoped BigOperators

def epochIndex (t : ℕ) : ℕ := Nat.log 2 (t + 1)

def epochLength (k : ℕ) : ℕ := 2 ^ k

def epochStart (k : ℕ) : ℕ := epochLength k - 1

theorem epochLength_pos (k : ℕ) : 0 < epochLength k := by
  exact pow_pos (by decide : 0 < (2 : ℕ)) _

theorem epochStart_le (t : ℕ) : epochStart (epochIndex t) ≤ t := by
  have h := Nat.pow_log_le_self 2 (by omega : t + 1 ≠ 0)
  dsimp [epochStart, epochLength, epochIndex]
  omega

theorem round_lt_epochEnd (t : ℕ) : t < epochStart (epochIndex t) +
    epochLength (epochIndex t) := by
  have h := Nat.lt_pow_succ_log_self (by decide : 1 < (2 : ℕ)) (t + 1)
  have hpos := epochLength_pos (epochIndex t)
  dsimp [epochStart, epochLength, epochIndex] at *
  rw [pow_succ] at h
  omega

theorem epochIndex_eq_of_mem {t k : ℕ}
    (hlo : epochStart k ≤ t) (hhi : t < epochStart k + epochLength k) :
    epochIndex t = k := by
  have hpos := epochLength_pos k
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · dsimp [epochStart, epochLength] at *
    omega
  · dsimp [epochStart, epochLength] at *
    rw [pow_succ]
    omega

@[simp] theorem epochIndex_at_start (k : ℕ) : epochIndex (epochStart k) = k := by
  apply epochIndex_eq_of_mem (le_refl _)
  have := epochLength_pos k
  omega

theorem epochIndex_mem (t : ℕ) : epochStart (epochIndex t) ≤ t ∧
    t < epochStart (epochIndex t) + epochLength (epochIndex t) :=
  ⟨epochStart_le t, round_lt_epochEnd t⟩

theorem epochIndex_eq_iff (t k : ℕ) : epochIndex t = k ↔
    epochStart k ≤ t ∧ t < epochStart k + epochLength k := by
  constructor
  · intro h
    simpa [h] using epochIndex_mem t
  · rintro ⟨hlo, hhi⟩
    exact epochIndex_eq_of_mem hlo hhi

/-- The final epoch may be truncated; every earlier occupied epoch has full length. -/
def epochCount (T k : ℕ) : ℕ := min (epochLength k) (T - epochStart k)

abbrev EpochBlock (T k : ℕ) := { t : Fin T // epochIndex t.val = k }

/-- The actual positions in an epoch of a finite prefix are exactly an initial
segment of the rule epoch clock. No full-length final block is assumed. -/
def epochBlockEquiv (T k : ℕ) : EpochBlock T k ≃ Fin (epochCount T k) where
  toFun t := ⟨t.val.val - epochStart k, by
    have hmem := (epochIndex_eq_iff t.val.val k).1 t.property
    dsimp [epochCount]
    apply Nat.lt_min.mpr
    exact ⟨by omega, by have := t.val.isLt; omega⟩⟩
  invFun i := ⟨⟨epochStart k + i.val, by
    have hi' : i.val < T - epochStart k := (Nat.lt_min.mp i.isLt).2
    omega⟩, by
    change epochIndex (epochStart k + i.val) = k
    apply epochIndex_eq_of_mem (by omega)
    have hi : i.val < epochLength k := (Nat.lt_min.mp i.isLt).1
    omega⟩
  left_inv t := by
    apply Subtype.ext
    apply Fin.ext
    have hmem := (epochIndex_eq_iff t.val.val k).1 t.property
    simp only
    omega
  right_inv i := by
    apply Fin.ext
    simp

@[simp] theorem epochBlockEquiv_symm_val (T k : ℕ) (i : Fin (epochCount T k)) :
    ((epochBlockEquiv T k).symm i).val.val = epochStart k + i.val := rfl

theorem epochCount_le_length (T k : ℕ) : epochCount T k ≤ epochLength k :=
  Nat.min_le_left _ _

theorem epochIndex_lt_prefix (T : ℕ) (t : Fin T) :
    epochIndex t.val < Nat.log 2 T + 1 := by
  have hm : t.val + 1 ≤ T := by omega
  have := Nat.log_mono_right (b := 2) hm
  dsimp [epochIndex]
  omega

def epochLabel (T : ℕ) (t : Fin T) : Fin (Nat.log 2 T + 1) :=
  ⟨epochIndex t.val, epochIndex_lt_prefix T t⟩

def epochFiberEquiv (T : ℕ) (k : Fin (Nat.log 2 T + 1)) :
    { t : Fin T // epochLabel T t = k } ≃ Fin (epochCount T k.val) :=
  (Equiv.subtypeEquivRight (fun t => by
    simp only [epochLabel, Fin.ext_iff])).trans (epochBlockEquiv T k.val)

@[simp] theorem epochFiberEquiv_symm_val (T : ℕ) (k : Fin (Nat.log 2 T + 1))
    (i : Fin (epochCount T k.val)) :
    ((epochFiberEquiv T k).symm i).val.val = epochStart k.val + i.val := rfl

/-- The stream presentation of a restarted family. Unlike a fixed-horizon rule,
the epoch budget is computed from the current clock, and never from a terminal
horizon. -/
def restartStream (rule : ℕ → (ℕ → Bool) → ℕ → ℝ) (y : ℕ → Bool) (t : ℕ) : ℝ :=
  let k := epochIndex t
  rule (epochLength k) (fun i => y (epochStart k + i)) (t - epochStart k)

theorem restartStream_causal (rule : ℕ → (ℕ → Bool) → ℕ → ℝ)
    (hlocal : ∀ L y z t, (∀ i < t, y i = z i) → rule L y t = rule L z t)
    {y z : ℕ → Bool} {t : ℕ} (h : ∀ i < t, y i = z i) :
    restartStream rule y t = restartStream rule z t := by
  apply hlocal
  intro i hi
  apply h
  have hs := epochStart_le t
  omega

theorem restartStream_on_epoch (rule : ℕ → (ℕ → Bool) → ℕ → ℝ)
    (y : ℕ → Bool) (k i : ℕ) (hi : i < epochLength k) :
    restartStream rule y (epochStart k + i) =
      rule (epochLength k) (fun j => y (epochStart k + j)) i := by
  have hk : epochIndex (epochStart k + i) = k :=
    epochIndex_eq_of_mem (by omega) (by omega)
  simp [restartStream, hk]

/-- Restart an arbitrary family of deterministic rule forecasting rules. The
only input is the already observed outcome history; there is no terminal horizon.
`rule L h` is the prediction with epoch budget `L` and rule history `h`. -/
def restartForecast (rule : ℕ → List Bool → ℝ) (history : List Bool) : ℝ :=
  let k := epochIndex history.length
  rule (epochLength k) (history.drop (epochStart k))

/-- The infinite output sequence of one deterministic restarted forecaster. -/
def restartSequence (rule : ℕ → List Bool → ℝ) (y : ℕ → Bool) (t : ℕ) : ℝ :=
  restartForecast rule (List.ofFn (fun i : Fin t => y i))

theorem restartSequence_causal (rule : ℕ → List Bool → ℝ)
    {y z : ℕ → Bool} {t : ℕ} (h : ∀ i < t, y i = z i) :
    restartSequence rule y t = restartSequence rule z t := by
  unfold restartSequence
  congr 1
  apply congrArg List.ofFn
  funext i
  exact h i i.isLt

theorem restartForecast_valid (rule : ℕ → List Bool → ℝ)
    (h : ∀ L history, rule L history ∈ Set.Icc (0 : ℝ) 1) (history : List Bool) :
    restartForecast rule history ∈ Set.Icc (0 : ℝ) 1 := h _ _

theorem sqrt_two_gt_one : 1 < Real.sqrt 2 := by
  have h := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hnonneg := Real.sqrt_nonneg (2 : ℝ)
  nlinarith

theorem sqrt_pow_two (k : ℕ) : Real.sqrt ((2 : ℝ) ^ k) = (Real.sqrt 2) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- Exact geometric identity in the second line of (7.2). -/
theorem sum_sqrt_dyadic (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), Real.sqrt ((2 : ℝ) ^ j)) =
      (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ k) - (1 + Real.sqrt 2) := by
  have hs : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  simp_rw [sqrt_pow_two]
  induction k with
  | zero => norm_num
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    have hsqk := congrArg (fun z : ℝ => z * (Real.sqrt 2) ^ k) hs
    nlinarith

/-- Every truncated dyadic geometric sum is strictly below the anytime constant
at every horizon reaching its last epoch. -/
theorem sum_sqrt_dyadic_lt {T k : ℕ} (h : 2 ^ k ≤ T) :
    (∑ j ∈ Finset.range (k + 1), Real.sqrt ((2 : ℝ) ^ j)) <
      (2 + Real.sqrt 2) * Real.sqrt (T : ℝ) := by
  rw [sum_sqrt_dyadic]
  have hc : 0 ≤ 2 + Real.sqrt 2 := by positivity
  have hroot : Real.sqrt ((2 : ℝ) ^ k) ≤ Real.sqrt (T : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast h
  have hm := mul_le_mul_of_nonneg_left hroot hc
  have hp := Real.sqrt_nonneg (2 : ℝ)
  linarith

theorem sum_sqrt_epochs_lt (T : ℕ) (hT : 0 < T) :
    (∑ j ∈ Finset.range (Nat.log 2 T + 1), Real.sqrt ((2 : ℝ) ^ j)) <
      (2 + Real.sqrt 2) * Real.sqrt (T : ℝ) := by
  exact sum_sqrt_dyadic_lt (Nat.pow_log_le_self 2 (by omega))

/-- The optimized finite rule, including an irrelevant default for budget zero.
Every actual dyadic epoch has positive budget. -/
def optimizedBudgetRule (L : ℕ) (y : ℕ → Bool) (t : ℕ) : ℝ :=
  if hL : 0 < L then
    let hm : 0 < optimalGrid L := by
      have h := (optimalGrid_threshold L (by omega)).1
      omega
    gridForecast hm (gridRun hm y t)
  else 1 / 2

theorem optimizedBudgetRule_causal (L : ℕ) (y z : ℕ → Bool) (t : ℕ)
    (h : ∀ i < t, y i = z i) :
    optimizedBudgetRule L y t = optimizedBudgetRule L z t := by
  unfold optimizedBudgetRule
  split_ifs with hL
  · exact gridForecast_nonanticipating _ _ _ _ h
  · rfl

theorem optimizedBudgetRule_mem (L : ℕ) (y : ℕ → Bool) (t : ℕ) :
    optimizedBudgetRule L y t ∈ Set.Icc (0 : ℝ) 1 := by
  unfold optimizedBudgetRule
  split_ifs with hL
  · exact gridForecast_mem _ _
  · constructor <;> norm_num

/-- A single infinite deterministic prediction stream with dyadic resets. -/
def anytimePrediction (y : ℕ → Bool) (t : ℕ) : ℝ :=
  restartStream optimizedBudgetRule y t

theorem anytimePrediction_causal {y z : ℕ → Bool} {t : ℕ}
    (h : ∀ i < t, y i = z i) : anytimePrediction y t = anytimePrediction z t :=
  restartStream_causal _ optimizedBudgetRule_causal h

theorem anytimePrediction_mem (y : ℕ → Bool) (t : ℕ) :
    anytimePrediction y t ∈ Set.Icc (0 : ℝ) 1 := optimizedBudgetRule_mem _ _ _

theorem optimizedBudgetRule_prefix_bound (L n : ℕ) (hL : 0 < L) (hn : n ≤ L)
    (y : ℕ → Bool) :
    calDist (fun t : Fin n => optimizedBudgetRule L y t.val) (runOutcomes y n) ≤
      Real.sqrt (L : ℝ) := by
  have hm : 0 < optimalGrid L := by
    have h := (optimalGrid_threshold L (by omega)).1
    omega
  have hgrid := fixed_grid_pathwise_bound hm y n
  have heq : (fun t : Fin n => optimizedBudgetRule L y t.val) = runForecast hm y n := by
    funext t
    simp [optimizedBudgetRule, hL, runForecast]
  rw [heq]
  have hn' : (n : ℝ) ≤ L := by exact_mod_cast hn
  have hden : (0 : ℝ) ≤ 2 * (optimalGrid L : ℝ) := by positivity
  have hmono := div_le_div_of_nonneg_right hn' hden
  have hopt := optimalValue_lt_sqrt L (by omega)
  unfold optimalValue gridObjective at hopt
  linarith

/-- Each genuine block, including a truncated last block, has the bound for
the budget used when that block began. -/
theorem anytime_epoch_bound (y : ℕ → Bool) (T : ℕ)
    (k : Fin (Nat.log 2 T + 1)) :
    calDist (fun t : { t : Fin T // epochLabel T t = k } => anytimePrediction y t.val.val)
      (fun t : { t : Fin T // epochLabel T t = k } => binaryValue (y t.val.val)) ≤
      Real.sqrt ((2 : ℝ) ^ k.val) := by
  classical
  let e := epochFiberEquiv T k
  let ys : ℕ → Bool := fun i => y (epochStart k.val + i)
  have hp : (fun i : Fin (epochCount T k.val) =>
      anytimePrediction y (e.symm i).val.val) =
      (fun i : Fin (epochCount T k.val) => optimizedBudgetRule (epochLength k.val) ys i.val) := by
    funext i
    change restartStream optimizedBudgetRule y
      (epochStart k.val + i.val) = _
    exact restartStream_on_epoch _ _ _ _
      (lt_of_lt_of_le i.isLt (epochCount_le_length T k.val))
  have hy : (fun i : Fin (epochCount T k.val) => binaryValue (y (e.symm i).val.val)) =
      runOutcomes ys (epochCount T k.val) := by
    funext i
    rfl
  have hreindex := calDist_equiv e.symm
    (fun t : { t : Fin T // epochLabel T t = k } => anytimePrediction y t.val.val)
    (fun t : { t : Fin T // epochLabel T t = k } => binaryValue (y t.val.val))
  simp only [Function.comp_def] at hreindex
  rw [← hreindex, hp, hy]
  have hb := optimizedBudgetRule_prefix_bound (epochLength k.val) (epochCount T k.val)
    (epochLength_pos _) (epochCount_le_length _ _) ys
  simpa [epochLength] using hb

/-- The pathwise distance part of Corollary 2.2, with one forecaster and every
infinite outcome path and every positive prefix of that same run. -/
theorem anytime_pathwise_bound (y : ℕ → Bool) (T : ℕ) (hT : 1 ≤ T) :
    calDist (fun t : Fin T => anytimePrediction y t.val) (runOutcomes y T) <
      (2 + Real.sqrt 2) * Real.sqrt (T : ℝ) := by
  classical
  have hp := calDist_partition_le (epochLabel T)
    (fun t : Fin T => anytimePrediction y t.val) (runOutcomes_mem y T)
  have hs : (∑ k : Fin (Nat.log 2 T + 1),
      calDist (fun t : { t : Fin T // epochLabel T t = k } => anytimePrediction y t.val.val)
        (fun t : { t : Fin T // epochLabel T t = k } => binaryValue (y t.val.val))) ≤
      ∑ k : Fin (Nat.log 2 T + 1), Real.sqrt ((2 : ℝ) ^ k.val) := by
    exact Finset.sum_le_sum fun k _ => anytime_epoch_bound y T k
  have hsum := sum_sqrt_epochs_lt T (by omega)
  rw [← Fin.sum_univ_eq_sum_range] at hsum
  exact (hp.trans hs).trans_lt hsum

/-- An actual deterministic rule whose only input at clock `t` is the outcome
prefix of length `t`. The false extension is irrelevant by causality. -/
def anytimeForecaster (t : ℕ) (history : Fin t → Bool) : Set.Icc (0 : ℝ) 1 :=
  ⟨anytimePrediction (fun i => if hi : i < t then history ⟨i, hi⟩ else false) t,
    anytimePrediction_mem _ _⟩

theorem anytimeForecaster_path (y : ℕ → Bool) (t : ℕ) :
    (anytimeForecaster t (fun i => y i.val)).val = anytimePrediction y t := by
  change anytimePrediction (fun i => if hi : i < t then y i else false) t =
    anytimePrediction y t
  apply anytimePrediction_causal (t := t)
  intro i hi
  simp [hi]

/-- Horizon-independent existence with the quantifiers of Corollary 2.2. -/
theorem horizon_free_guarantee :
    ∃ F : (t : ℕ) → (Fin t → Bool) → Set.Icc (0 : ℝ) 1,
      ∀ (y : ℕ → Bool) (T : ℕ), 1 ≤ T →
        calDist (fun t : Fin T => (F t.val (fun i => y i.val)).val) (runOutcomes y T) <
          (2 + Real.sqrt 2) * Real.sqrt (T : ℝ) := by
  refine ⟨anytimeForecaster, ?_⟩
  intro y T hT
  simp only [anytimeForecaster_path]
  exact anytime_pathwise_bound y T hT

/-- The next epoch's number of grid nodes (including its extra endpoint)
fits a budget of two node initializations per current round. This is the
arithmetic scheduling fact in Appendix B.2. -/
theorem next_grid_node_budget (L : ℕ) (hL : 1 ≤ L) :
    optimalGrid (2 * L) + 1 ≤ 2 * L := by
  have hgrid : optimalGrid (2 * L) ≤ L := by
    apply (optimalGrid_le_iff (2 * L) L (by omega)).2
    nlinarith
  omega

/-- Progress counter for initializing two of the next epoch's nodes on each
current round. The known sorted nodes may be initialized in this order. -/
def nextGridInitialized (L rounds : ℕ) : ℕ :=
  min (optimalGrid (2 * L) + 1) (2 * rounds)

@[simp] theorem nextGridInitialized_zero (L : ℕ) : nextGridInitialized L 0 = 0 := by
  simp [nextGridInitialized]

theorem nextGridInitialized_step (L rounds : ℕ) :
    nextGridInitialized L rounds ≤ nextGridInitialized L (rounds + 1) ∧
    nextGridInitialized L (rounds + 1) ≤ nextGridInitialized L rounds + 2 := by
  dsimp [nextGridInitialized]
  omega

theorem nextGridInitialized_complete (L : ℕ) (hL : 1 ≤ L) :
    nextGridInitialized L L = optimalGrid (2 * L) + 1 := by
  exact Nat.min_eq_left (next_grid_node_budget L hL)

theorem dyadic_grid_size_lt (k : ℕ) :
    (optimalGrid (2 ^ k) : ℝ) < 2 * Real.sqrt ((2 : ℝ) ^ k) := by
  have hL : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by norm_num)
  have h := (optimalGrid_sqrt_bounds (2 ^ k) hL).2
  have hcast : (1 : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hL
  have hroot : (1 : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ k) := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hcast
  simp only [Nat.cast_pow, Nat.cast_ofNat] at h
  linarith

/-- Sum of all grid parameters ever allocated through a prefix, including
the next prepared epoch. This accounts for retired epochs as well as the
current and future epoch; it is an arithmetic bound, not a data-structure
time-complexity assertion. -/
theorem all_allocated_grid_sizes_lt (T : ℕ) (hT : 1 ≤ T) :
    (∑ k ∈ Finset.range (Nat.log 2 T + 2), (optimalGrid (2 ^ k) : ℝ)) <
      12 * Real.sqrt (T : ℝ) := by
  let K := Nat.log 2 T
  have hsum : (∑ k ∈ Finset.range (K + 2), (optimalGrid (2 ^ k) : ℝ)) <
      2 * (∑ k ∈ Finset.range (K + 2), Real.sqrt ((2 : ℝ) ^ k)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_lt_sum_of_nonempty ⟨0, by simp⟩
    intro k hk
    exact dyadic_grid_size_lt k
  have hpow : 2 ^ K ≤ T := Nat.pow_log_le_self 2 (by omega)
  have hroot : Real.sqrt ((2 : ℝ) ^ K) ≤ Real.sqrt (T : ℝ) := by
    apply Real.sqrt_le_sqrt
    exact_mod_cast hpow
  have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := Real.sq_sqrt (by norm_num)
  have hq := Real.sqrt_nonneg (2 : ℝ)
  have hqle : Real.sqrt (2 : ℝ) ≤ 2 := by nlinarith
  have hcoef : 2 * (2 + Real.sqrt 2) * Real.sqrt 2 ≤ (12 : ℝ) := by nlinarith
  have hC : 0 ≤ 2 * (2 + Real.sqrt 2) * Real.sqrt 2 := by positivity
  calc
    (∑ k ∈ Finset.range (K + 2), (optimalGrid (2 ^ k) : ℝ))
      < 2 * (∑ k ∈ Finset.range (K + 2), Real.sqrt ((2 : ℝ) ^ k)) := hsum
    _ ≤ 2 * (2 + Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ (K + 1)) := by
      rw [show K + 2 = (K + 1) + 1 by omega, sum_sqrt_dyadic]
      nlinarith
    _ = (2 * (2 + Real.sqrt 2) * Real.sqrt 2) * Real.sqrt ((2 : ℝ) ^ K) := by
      rw [pow_succ, Real.sqrt_mul (by positivity)]
      ring
    _ ≤ (2 * (2 + Real.sqrt 2) * Real.sqrt 2) * Real.sqrt (T : ℝ) :=
      mul_le_mul_of_nonneg_left hroot hC
    _ ≤ 12 * Real.sqrt (T : ℝ) :=
      mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)

/-- Endpoint-inclusive node counts have the same square-root bound. -/
theorem all_allocated_grid_nodes_lt (T : ℕ) (hT : 1 ≤ T) :
    (∑ k ∈ Finset.range (Nat.log 2 T + 2), ((optimalGrid (2 ^ k) + 1 : ℕ) : ℝ)) <
      24 * Real.sqrt (T : ℝ) := by
  have hsum : (∑ k ∈ Finset.range (Nat.log 2 T + 2), ((optimalGrid (2 ^ k) + 1 : ℕ) : ℝ)) ≤
      2 * (∑ k ∈ Finset.range (Nat.log 2 T + 2), (optimalGrid (2 ^ k) : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    have hL : 1 ≤ (2 : ℕ) ^ k := Nat.one_le_pow k 2 (by norm_num)
    have hm := (optimalGrid_threshold (2 ^ k) hL).1
    have hcast : (1 : ℝ) ≤ (optimalGrid (2 ^ k) : ℝ) := by exact_mod_cast hm
    push_cast
    linarith
  have h := all_allocated_grid_sizes_lt T hT
  linarith

end

end CalibrationDistance
