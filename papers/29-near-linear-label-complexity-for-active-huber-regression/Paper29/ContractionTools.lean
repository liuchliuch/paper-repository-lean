import Paper29.WeightLogMetric
import Mathlib.Algebra.Order.Archimedean.Basic

noncomputable section
namespace Paper29.WeightConstruction

variable {n : ℕ} [Nonempty (Fin n)] (F : PositiveWeights n → PositiveWeights n)
    (hF : ∀ u w, logDist (F u) (F w) ≤ (1/2)*logDist u w)

include hF

theorem contraction_successive (w : PositiveWeights n) (k : ℕ) :
    logDist (F^[k+1] w) (F^[k] w) ≤ (1/2:ℝ)^k * logDist (F w) w := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hh : logDist (F (F^[k+1] w)) (F (F^[k] w)) ≤
        (1/2:ℝ)^(k+1)*logDist (F w) w := by
      calc
        _ ≤ (1/2)*logDist (F^[k+1] w) (F^[k] w) := hF _ _
        _ ≤ (1/2)*((1/2:ℝ)^k*logDist (F w) w) :=
          mul_le_mul_of_nonneg_left ih (by norm_num)
        _ = _ := by rw [pow_succ]; ring
    simpa only [Function.iterate_succ_apply'] using hh

theorem contraction_stopping (w : PositiveWeights n) {ε : ℝ} (hε : 0 < ε) :
    ∃ k : ℕ, logDist (F (F^[k] w)) (F^[k] w) ≤ ε := by
  let D := logDist (F w) w
  have hD : 0 ≤ D := logDist_nonneg _ _
  obtain ⟨k,hk⟩ := exists_pow_lt_of_lt_one (div_pos hε (by linarith : 0 < D+1))
    (by norm_num : (1/2:ℝ)<1)
  refine ⟨k, ?_⟩
  have hh := contraction_successive F hF w k
  rw [Function.iterate_succ_apply'] at hh
  apply hh.trans
  have hp : 0 ≤ (1/2:ℝ)^k := by positivity
  have hm := (lt_div_iff₀ (by linarith : 0 < D+1)).1 hk
  change (1/2:ℝ)^k * D ≤ ε
  nlinarith

/-- A posteriori error at any known fixed point; no limiting sequence is
assumed as the output of a finite algorithm. -/
theorem contraction_fixedpoint_error (w v : PositiveWeights n) (hv : F v = v) :
    logDist w v ≤ 2 * logDist (F w) w := by
  have ht := logDist_triangle w (F w) v
  have hc := hF w v
  rw [hv] at hc
  rw [logDist_symm w (F w)] at ht
  linarith

end Paper29.WeightConstruction
