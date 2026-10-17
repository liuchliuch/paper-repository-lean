import Paper29.WeightLogMetric
import Paper29.WeightScalar
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
open scoped BigOperators Classical
namespace Paper29.WeightConstruction

variable {n d : ℕ} (A : Matrix (Fin n) (Fin d) ℝ) (hA : A.rank = d)
    (hrows : ∀ i, A i ≠ 0)

/-- The exact leverage update W_j, including its positivity proof. -/
def update (j : ℤ) (w : PositiveWeights n) : PositiveWeights n :=
  ⟨fun i => huber (Leverage.radius A w i) / ((2 : ℝ)^j * Leverage.radiusSq A w i), by
    intro i
    have hr := Leverage.radiusSq_pos A w (Leverage.mulVec_injective_of_rank_eq A hA)
      w.property i (hrows i)
    have hs : 0 < huber (Leverage.radius A w i) := by
      apply lt_of_le_of_ne (huber_nonneg _)
      intro h
      have hz := (huber_eq_zero_iff _).mp h.symm
      exact (ne_of_gt (Real.sqrt_pos.2 hr)) hz
    exact div_pos hs (mul_pos (zpow_pos (by norm_num) _) hr)⟩

private theorem log_update (j : ℤ) (w : PositiveWeights n) (i : Fin n) :
    Real.log (update A hA hrows j w i) =
      logFactor (Leverage.radiusSq A w i) - Real.log ((2 : ℝ)^j) := by
  have hr := Leverage.radiusSq_pos A w (Leverage.mulVec_injective_of_rank_eq A hA)
    w.property i (hrows i)
  change Real.log (huber (Real.sqrt (Leverage.radiusSq A w i)) /
    ((2 : ℝ)^j * Leverage.radiusSq A w i)) = _
  rw [Real.log_div (by
    exact ne_of_gt (lt_of_le_of_ne (huber_nonneg _) (by
      intro h
      exact (ne_of_gt (Real.sqrt_pos.2 hr)) ((huber_eq_zero_iff _).mp h.symm))))
    (ne_of_gt (mul_pos (zpow_pos (by norm_num) _) hr)),
    Real.log_mul (ne_of_gt (zpow_pos (by norm_num : (0 : ℝ)<2) j)) (ne_of_gt hr)]
  unfold logFactor
  ring

theorem update_contracts [Nonempty (Fin n)] (external : RadiusLogNonexpansive)
    (j : ℤ) (u w : PositiveWeights n) :
    logDist (update A hA hrows j u) (update A hA hrows j w) ≤ (1/2) * logDist u w := by
  apply logDist_le
  intro i
  rw [log_update, log_update, sub_sub_sub_cancel_right]
  have hu := Leverage.radiusSq_pos A u (Leverage.mulVec_injective_of_rank_eq A hA)
    u.property i (hrows i)
  have hw := Leverage.radiusSq_pos A w (Leverage.mulVec_injective_of_rank_eq A hA)
    w.property i (hrows i)
  exact (logFactor_lipschitz hu hw).trans
    (mul_le_mul_of_nonneg_left (external n d A hA hrows u w i) (by norm_num))

theorem update_next (j : ℤ) (w : PositiveWeights n) :
    update A hA hrows (j+1) w = rescale (1/2) (by norm_num) (update A hA hrows j w) := by
  apply Subtype.ext
  funext i
  change huber _ / ((2 : ℝ)^(j+1) * _) = (1/2) * (huber _ / ((2 : ℝ)^j * _))
  rw [zpow_add₀ (by norm_num : (2 : ℝ)≠0), zpow_one]
  ring

/-- Actual geometric convergence of successive exact iterates. -/
theorem successive_iterates [Nonempty (Fin n)] (external : RadiusLogNonexpansive)
    (j : ℤ) (w : PositiveWeights n) (k : ℕ) :
    logDist ((update A hA hrows j)^[k+1] w) ((update A hA hrows j)^[k] w) ≤
      (1/2 : ℝ)^k * logDist (update A hA hrows j w) w := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hnew : logDist (update A hA hrows j ((update A hA hrows j)^[k+1] w))
        (update A hA hrows j ((update A hA hrows j)^[k] w)) ≤
        (1/2 : ℝ)^(k+1) * logDist (update A hA hrows j w) w := by
      calc
        _ ≤ (1/2) * logDist ((update A hA hrows j)^[k+1] w)
            ((update A hA hrows j)^[k] w) := update_contracts A hA hrows external j _ _
        _ ≤ (1/2) * ((1/2 : ℝ)^k * logDist (update A hA hrows j w) w) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = (1/2 : ℝ)^(k+1) * logDist (update A hA hrows j w) w := by
          rw [pow_succ]
          ring
    simpa only [Function.iterate_succ_apply'] using hnew

/-- A finite stopping certificate; this is a proof of termination, not a
large numerical certificate to be evaluated. -/
theorem finite_stopping [Nonempty (Fin n)] (external : RadiusLogNonexpansive)
    (j : ℤ) (w : PositiveWeights n) :
    ∃ k : ℕ, logDist (update A hA hrows j ((update A hA hrows j)^[k] w))
      ((update A hA hrows j)^[k] w) ≤ Real.log 2 := by
  let D := logDist (update A hA hrows j w) w
  have hD : 0 ≤ D := logDist_nonneg _ _
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num)
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (div_pos hl (by linarith : 0 < D+1))
    (by norm_num : (1/2 : ℝ) < 1)
  refine ⟨k, ?_⟩
  have hbound := successive_iterates A hA hrows external j w k
  rw [Function.iterate_succ_apply'] at hbound
  apply hbound.trans
  have hp : 0 ≤ (1/2 : ℝ)^k := by positivity
  have hmul := (lt_div_iff₀ (by linarith : 0 < D+1)).1 hk
  change (1/2 : ℝ)^k * D ≤ Real.log 2
  nlinarith

/-- One warm-start update propagates the log4 residual invariant. -/
theorem warm_start [Nonempty (Fin n)] (external : RadiusLogNonexpansive)
    (j : ℤ) (w : PositiveWeights n)
    (hw : logDist (update A hA hrows j w) w ≤ Real.log 4) :
    logDist (update A hA hrows (j+1) (update A hA hrows (j+1) w))
      (update A hA hrows (j+1) w) ≤ Real.log 4 := by
  have hl : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hhalf : |Real.log (1/2 : ℝ)| = Real.log 2 := by
    rw [show (1/2 : ℝ) = (2:ℝ)⁻¹ by norm_num, Real.log_inv,
      abs_neg, abs_of_pos (Real.log_pos (by norm_num))]
  have hd : logDist (update A hA hrows (j+1) w) w ≤ Real.log 4 + Real.log 2 := by
    rw [update_next]
    exact (logDist_rescale_left _ (by norm_num) _ _).trans (by rw [hhalf]; linarith)
  have hc := update_contracts A hA hrows external (j+1) (update A hA hrows (j+1) w) w
  have hlog2 : 0 ≤ Real.log 2 := (Real.log_pos (by norm_num : (1:ℝ)<2)).le
  linarith

end Paper29.WeightConstruction
