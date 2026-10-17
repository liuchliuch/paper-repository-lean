import Paper37.RateUpper
import Paper37.ContinuationDP

/-! Appendix C.4: exact pathwise telescoping for the genuine source kernels
and the actual horizon-specific block assignment. -/
noncomputable section
namespace Paper37.SequentialRegret
open Finset Paper37.Renewal Paper37.Prediction Paper37.EnvelopeBridge
open Paper37.RenewalCompression Paper37.ContinuationDP Paper37.AnalyticBounds

lemma prefixMass_pos (N : ℕ) (z : List Bool) : 0 < prefixMass N z := by
  apply sum_pos'
  · intro v hv; exact (blockAssignment_pos _).le
  · refine ⟨List.replicate (N-z.length) false, ?_, blockAssignment_pos _⟩
    exact List.mem_toFinset.mpr ((mem_words _ _).mpr (by simp))

lemma prefixMass_step (N : ℕ) (z : List Bool) (hz : z.length < N) :
    prefixMass N z = prefixMass N (z ++ [false]) + prefixMass N (z ++ [true]) := by
  unfold prefixMass
  have hrem : N-z.length = (N-(z.length+1))+1 := by omega
  rw [hrem, sum_words_step]
  simp [List.append_assoc]

@[simp] lemma prefixMass_nil (N : ℕ) : prefixMass N [] = 1 := by
  simpa [prefixMass] using blockAssignment_sum N

@[simp] lemma prefixMass_full (x : List Bool) : prefixMass x.length x = blockAssignment x := by
  simp [prefixMass, words]

@[simp] lemma blockMass_nil (μ : Law) : blockMass μ [] = 1 := by
  have hh := blockMass_normalized μ 0
  simpa using hh

lemma blockMass_one_extension_le (μ : Law) (z : List Bool) (b : Bool) :
    blockMass μ (z ++ [b]) ≤ blockMass μ z := by
  have hc := blockMass_right_consistency μ z
  cases b <;> linarith [blockMass_nonneg μ (z ++ [false]), blockMass_nonneg μ (z ++ [true])]

lemma blockMass_append_le (μ : Law) (z v : List Bool) : blockMass μ (z ++ v) ≤ blockMass μ z := by
  induction v generalizing z with
  | nil => simp
  | cons b v ih =>
    have heq : z ++ b :: v = (z ++ [b]) ++ v := by simp
    rw [heq]
    exact (ih (z ++ [b])).trans (blockMass_one_extension_le μ z b)

lemma positive_prefix (μ : Law) (x : List Bool) (hp : 0 < blockMass μ x) (t : ℕ) :
    0 < blockMass μ (x.take t) := by
  have hh := blockMass_append_le μ (x.take t) (x.drop t)
  rw [List.take_append_drop] at hh
  exact hp.trans_le hh

/-- The actual Bernoulli next-symbol probability under the source assignment. -/
def assignmentNext (N : ℕ) (z : List Bool) (b : Bool) : ℝ :=
  if b then (blockConditional N z : ℝ) else 1 - (blockConditional N z : ℝ)

/-- Both symbols of the assignment's kernel are the ratios of their genuine
prefix masses. The zero-symbol identity uses right consistency. -/
theorem assignmentNext_eq_ratio (N : ℕ) (z : List Bool) (b : Bool) (hz : z.length < N) :
    assignmentNext N z b = (prefixMass N (z ++ [b]) : ℝ) / (prefixMass N z : ℝ) := by
  have hq : (prefixMass N z : ℝ) ≠ 0 := by exact_mod_cast (prefixMass_pos N z).ne'
  cases b with
  | true => simp [assignmentNext, blockConditional]
  | false =>
    have hc := congrArg (fun q : ℚ => (q : ℝ)) (prefixMass_step N z hz)
    push_cast at hc
    simp only [assignmentNext, Bool.false_eq_true, if_false, blockConditional, Rat.cast_div]
    apply (eq_div_iff hq).mpr
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hq]
    linarith

lemma next_eq_ratio (μ : Law) (z : List Bool) (b : Bool) (hz : 0 < blockMass μ z) :
    next μ z b = blockMass μ (z ++ [b]) / blockMass μ z := by
  apply (eq_div_iff hz.ne').mpr
  rw [mul_comm]
  exact weighted_next μ z b

lemma sum_increments (f : ℕ → ℝ) (N : ℕ) :
    (∑ t ∈ range N, (f (t+1) - f t)) = f N - f 0 := by
  induction N with
  | zero => simp
  | succ N ih => rw [sum_range_succ, ih]; ring

/-- Exact C.13 equality on every positive source word. No averaged-risk
hypothesis replaces the pathwise positivity assumption. -/
theorem path_log_identity (μ : Law) (x : List Bool) (hp : 0 < blockMass μ x) :
    (∑ t ∈ range x.length,
      Real.log (next μ (x.take t) ((x[t]?).getD false) /
        assignmentNext x.length (x.take t) ((x[t]?).getD false))) =
      Real.log (blockMass μ x / (blockAssignment x : ℝ)) := by
  let f : ℕ → ℝ := fun t => Real.log (blockMass μ (x.take t)) -
    Real.log (prefixMass x.length (x.take t) : ℝ)
  have hterm (t : ℕ) (ht : t ∈ range x.length) :
      Real.log (next μ (x.take t) ((x[t]?).getD false) /
        assignmentNext x.length (x.take t) ((x[t]?).getD false)) = f (t+1)-f t := by
    have ht' : t < x.length := mem_range.mp ht
    have htake : x.take (t+1) = x.take t ++ [(x[t]?).getD false] := by
      simpa only [List.getElem?_eq_getElem ht', Option.getD_some] using
        List.take_succ_eq_append_getElem ht'
    have hp0 := positive_prefix μ x hp t
    have hp1 := positive_prefix μ x hp (t+1)
    have hq0 : 0 < (prefixMass x.length (x.take t) : ℝ) := by exact_mod_cast prefixMass_pos _ _
    have hq1 : 0 < (prefixMass x.length (x.take (t+1)) : ℝ) := by exact_mod_cast prefixMass_pos _ _
    have hlt : (x.take t).length < x.length := by simp [List.length_take, Nat.min_eq_left ht'.le]; omega
    rw [next_eq_ratio μ _ _ hp0, assignmentNext_eq_ratio _ _ _ hlt, ← htake]
    rw [Real.log_div (div_ne_zero hp1.ne' hp0.ne') (div_ne_zero hq1.ne' hq0.ne'),
      Real.log_div hp1.ne' hp0.ne', Real.log_div hq1.ne' hq0.ne']
    dsimp [f]
    ring
  rw [sum_congr rfl hterm, sum_increments]
  have hq : (blockAssignment x : ℝ) ≠ 0 := by exact_mod_cast (blockAssignment_pos x).ne'
  simp only [f, List.take_length, List.take_zero, prefixMass_full, prefixMass_nil,
    blockMass_nil, Rat.cast_one, Real.log_one, sub_self, sub_zero]
  exact (Real.log_div hp.ne' hq).symm

/-- The pathwise regret upper bound in C.13 for the actual renewal source and
actual first-renewal block assignment. -/
theorem path_log_regret (μ : Law) (x : List Bool) (hp : 0 < blockMass μ x) :
    (∑ t ∈ range x.length,
      Real.log (next μ (x.take t) ((x[t]?).getD false) /
        assignmentNext x.length (x.take t) ((x[t]?).getD false))) ≤
      redundancyBound x.length := by
  rw [path_log_identity μ x hp]
  exact Paper37.RateUpper.pointwise_block_regret μ x hp

/-- The computed conditional is exactly the one used by the pathwise kernel. -/
theorem assignmentNext_eq_computed (N : ℕ) (z : List Bool) (b : Bool) (hz : z.length < N) :
    assignmentNext N z b =
      if b then (evaluateConditional N z : ℝ) else 1 - (evaluateConditional N z : ℝ) := by
  rw [evaluateConditional_correct N z hz]
  rfl

end Paper37.SequentialRegret

namespace Paper37.SequentialRegret
open Finset Paper37.Renewal Paper37.Prediction Paper37.EnvelopeBridge
open Paper37.RenewalCompression Paper37.ContinuationDP Paper37.AnalyticBounds

/-- C.13 for the actual executed on-path conditional batch. -/
theorem computed_path_log_identity (μ : Law) (x : List Bool) (hp : 0 < blockMass μ x) :
    (∑ t ∈ range x.length,
      Real.log (next μ (x.take t) ((x[t]?).getD false) /
        (if (x[t]?).getD false then (evaluateConditional x.length (x.take t) : ℝ)
          else 1 - (evaluateConditional x.length (x.take t) : ℝ)))) =
      Real.log (blockMass μ x / (blockAssignment x : ℝ)) := by
  rw [← path_log_identity μ x hp]
  apply sum_congr rfl
  intro t ht
  have ht' : t < x.length := mem_range.mp ht
  have hlt : (x.take t).length < x.length := by
    simp only [List.length_take, Nat.min_eq_left ht'.le]
    exact ht'
  rw [assignmentNext_eq_computed _ _ _ hlt]

/-- The finite-time `B_N` bound for the executed supplied forward path. -/
theorem computed_path_log_regret (μ : Law) (x : List Bool) (hp : 0 < blockMass μ x) :
    (∑ t ∈ range x.length,
      Real.log (next μ (x.take t) ((x[t]?).getD false) /
        (if (x[t]?).getD false then (evaluateConditional x.length (x.take t) : ℝ)
          else 1 - (evaluateConditional x.length (x.take t) : ℝ)))) ≤
      redundancyBound x.length := by
  rw [computed_path_log_identity μ x hp]
  exact Paper37.RateUpper.pointwise_block_regret μ x hp

end Paper37.SequentialRegret
