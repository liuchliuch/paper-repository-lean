import Paper29.WeightIteration

noncomputable section
open scoped BigOperators Classical
namespace Paper29.WeightConstruction

variable {n d : ℕ} [Nonempty (Fin n)]
    (A : Matrix (Fin n) (Fin d) ℝ) (hA : A.rank = d) (hrows : ∀ i, A i ≠ 0)

theorem residual_coordinate_bounds (j : ℤ) (w : PositiveWeights n)
    (hw : logDist (update A hA hrows j w) w ≤ Real.log 4) (i : Fin n) :
    w i / 4 ≤ update A hA hrows j w i ∧ update A hA hrows j w i ≤ 4 * w i := by
  have h := (coordinate_le_logDist (update A hA hrows j w) w i).trans hw
  obtain ⟨hlo, hhi⟩ := abs_le.mp h
  have hup := (update A hA hrows j w).property i
  have hwpos := w.property i
  constructor
  · apply (Real.log_le_log_iff (div_pos hwpos (by norm_num)) hup).mp
    rw [Real.log_div (ne_of_gt hwpos) (by norm_num : (4:ℝ)≠0)]
    linarith
  · apply (Real.log_le_log_iff hup (mul_pos (by norm_num) hwpos)).mp
    rw [Real.log_mul (by norm_num : (4:ℝ)≠0) (ne_of_gt hwpos)]
    linarith

/-- The log residual is converted to the exact approximate-scheme inequalities
(3.8), with the universal constant alpha=4. -/
theorem residual_scheme_bounds (j : ℤ) (w : PositiveWeights n)
    (hw : logDist (update A hA hrows j w) w ≤ Real.log 4) (i : Fin n) :
    (2 : ℝ)^j / 4 ≤ huber (Leverage.radius A w i) / Leverage.leverage A w i ∧
      huber (Leverage.radius A w i) / Leverage.leverage A w i ≤ 4 * (2 : ℝ)^j := by
  have hr := Leverage.radiusSq_pos A w (Leverage.mulVec_injective_of_rank_eq A hA)
    w.property i (hrows i)
  have hwi := w.property i
  obtain ⟨hlo, hhi⟩ := residual_coordinate_bounds A hA hrows j w hw i
  have hlow : (1/4 : ℝ) ≤ update A hA hrows j w i / w i :=
    (le_div_iff₀ hwi).2 (by linarith)
  have hhigh : update A hA hrows j w i / w i ≤ 4 := (div_le_iff₀ hwi).2 hhi
  have he : huber (Leverage.radius A w i) / Leverage.leverage A w i =
      (2 : ℝ)^j * (update A hA hrows j w i / w i) := by
    change huber _ / (w i * Leverage.radiusSq A w i) =
      (2 : ℝ)^j * ((huber _ / ((2 : ℝ)^j * Leverage.radiusSq A w i)) / w i)
    field_simp
  rw [he]
  have hz : 0 ≤ (2 : ℝ)^j := (zpow_pos (by norm_num) j).le
  constructor
  · convert mul_le_mul_of_nonneg_left hlow hz using 1 <;> ring
  · simpa only [mul_comm] using mul_le_mul_of_nonneg_left hhigh hz

/-- The stopping index is the least successful finite index. -/
def firstStop (external : RadiusLogNonexpansive) (j : ℤ) (w : PositiveWeights n) : ℕ :=
  Nat.find (finite_stopping A hA hrows external j w)

def initialWeight (external : RadiusLogNonexpansive) (j : ℤ) : PositiveWeights n :=
  (update A hA hrows j)^[firstStop A hA hrows external j ⟨fun _ => 1, fun _ => by norm_num⟩]
    ⟨fun _ => 1, fun _ => by norm_num⟩

theorem initialWeight_residual (external : RadiusLogNonexpansive) (j : ℤ) :
    logDist (update A hA hrows j (initialWeight A hA hrows external j))
      (initialWeight A hA hrows external j) ≤ Real.log 4 := by
  have h := Nat.find_spec (finite_stopping A hA hrows external j
    ⟨fun _ => 1, fun _ => by norm_num⟩)
  exact h.trans (Real.log_le_log (by norm_num) (by norm_num))

/-- Each requested finite prefix makes one exact update per subsequent scale. -/
def sequence (j₀ : ℤ) (w₀ : PositiveWeights n) : ℕ → PositiveWeights n
  | 0 => w₀
  | k+1 => update A hA hrows (j₀ + (k:ℤ) + 1) (sequence j₀ w₀ k)

theorem sequence_residual (external : RadiusLogNonexpansive) (j₀ : ℤ)
    (w₀ : PositiveWeights n)
    (hw₀ : logDist (update A hA hrows j₀ w₀) w₀ ≤ Real.log 4) (k : ℕ) :
    logDist (update A hA hrows (j₀ + (k:ℤ)) (sequence A hA hrows j₀ w₀ k))
      (sequence A hA hrows j₀ w₀ k) ≤ Real.log 4 := by
  induction k with
  | zero => simpa only [Nat.cast_zero, add_zero, sequence] using hw₀
  | succ k ih =>
    have h := warm_start A hA hrows external (j₀ + (k:ℤ))
      (sequence A hA hrows j₀ w₀ k) ih
    simpa only [sequence, Nat.cast_add, Nat.cast_one, add_assoc] using h

theorem sequence_step_le (external : RadiusLogNonexpansive) (j₀ : ℤ)
    (w₀ : PositiveWeights n)
    (hw₀ : logDist (update A hA hrows j₀ w₀) w₀ ≤ Real.log 4) (k : ℕ) (i : Fin n) :
    sequence A hA hrows j₀ w₀ (k+1) i ≤ 2 * sequence A hA hrows j₀ w₀ k i := by
  have hr := sequence_residual A hA hrows external j₀ w₀ hw₀ k
  have hh := (residual_coordinate_bounds A hA hrows (j₀+(k:ℤ)) _ hr i).2
  change update A hA hrows ((j₀+(k:ℤ))+1) _ i ≤ _
  rw [update_next]
  change (1/2 : ℝ) * update A hA hrows (j₀+(k:ℤ)) _ i ≤ _
  linarith

include hA hrows

/-- The deterministic finite-prefix construction, with all positivity, scale
normalization, adjacent-scale control and exact mass conclusions derived. -/
theorem constructed_scheme (external : RadiusLogNonexpansive) (j₀ : ℤ) :
    ∃ w : ℕ → PositiveWeights n,
      (∀ (k : ℕ) (i : Fin n), (2:ℝ)^(j₀+(k:ℤ))/4 ≤
          huber (Leverage.radius A (w k) i) / Leverage.leverage A (w k) i ∧
        huber (Leverage.radius A (w k) i) / Leverage.leverage A (w k) i ≤
          4*(2:ℝ)^(j₀+(k:ℤ))) ∧
      (∀ k i, w (k+1) i ≤ 2 * w k i) ∧
      (∀ k, (∑ i, Leverage.leverage A (w k) i) = (d:ℝ)) := by
  let w₀ := initialWeight A hA hrows external j₀
  have hw₀ := initialWeight_residual A hA hrows external j₀
  refine ⟨sequence A hA hrows j₀ w₀, ?_, ?_, ?_⟩
  · intro k i
    exact residual_scheme_bounds A hA hrows _ _
      (sequence_residual A hA hrows external j₀ w₀ hw₀ k) i
  · exact sequence_step_le A hA hrows external j₀ w₀ hw₀
  · intro k
    exact Leverage.leverage_sum_of_rank_eq A _ hA (fun i => (sequence A hA hrows j₀ w₀ k).property i)

end Paper29.WeightConstruction
