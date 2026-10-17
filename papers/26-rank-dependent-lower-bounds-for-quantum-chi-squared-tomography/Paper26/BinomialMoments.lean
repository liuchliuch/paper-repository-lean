import Paper26.CollectiveSubmatrix

/-!
# Native moments of the actual retained-copy binomial law

The only combinatorial ingredient is Pascal's identity in mathlib's
`Finset.sum_choose_succ_mul`. Finite sums give the first and second moments,
including N=0 and w=0,1. Thus the existing `BinomialMomentsInput` has an actual
local witness; no moment, loss, or risk bound is assumed here.
-/

noncomputable section
open scoped BigOperators NNReal ENNReal

namespace Paper26.BinomialMoments
open CollectiveSubmatrix

/-- The finite binomial sum, written over natural counts. -/
def rawSum (N : ℕ) (w : ℝ) (f : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Finset.range (N + 1),
    (N.choose m : ℝ) * (w ^ m * (1 - w) ^ (N - m) * f m)

lemma rawSum_add (N : ℕ) (w : ℝ) (f g : ℕ → ℝ) :
    rawSum N w (fun m => f m + g m) = rawSum N w f + rawSum N w g := by
  simp [rawSum, mul_add, Finset.sum_add_distrib]

lemma rawSum_const_mul (N : ℕ) (w a : ℝ) (f : ℕ → ℝ) :
    rawSum N w (fun m => a * f m) = a * rawSum N w f := by
  unfold rawSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- Pascal recursion, with the next Bernoulli trial made explicit. -/
lemma rawSum_succ (N : ℕ) (w : ℝ) (f : ℕ → ℝ) :
    rawSum (N + 1) w f =
      (1 - w) * rawSum N w f + w * rawSum N w (fun m => f (m + 1)) := by
  unfold rawSum
  rw [show N + 1 + 1 = N + 2 by omega,
    Finset.sum_choose_succ_mul (fun i j => w ^ i * (1 - w) ^ j * f i) N]
  rw [Finset.mul_sum, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro m hm
    have hmN : m ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hm)
    rw [show N + 1 - m = (N - m) + 1 by omega, pow_succ]
    ring
  · apply Finset.sum_congr rfl
    intro m _
    rw [pow_succ]
    ring

lemma rawSum_one (N : ℕ) (w : ℝ) : rawSum N w (fun _ => 1) = 1 := by
  induction N with
  | zero => simp [rawSum]
  | succ N ih =>
    rw [rawSum_succ, ih]
    ring

lemma rawSum_const (N : ℕ) (w a : ℝ) : rawSum N w (fun _ => a) = a := by
  simpa only [mul_one, rawSum_one] using rawSum_const_mul N w a (fun _ => 1)

theorem rawSum_first (N : ℕ) (w : ℝ) :
    rawSum N w (fun m => (m : ℝ)) = N * w := by
  induction N with
  | zero => simp [rawSum]
  | succ N ih =>
    rw [rawSum_succ]
    have hshift : rawSum N w (fun m => ((m + 1 : ℕ) : ℝ)) = N * w + 1 := by
      simp only [Nat.cast_add, Nat.cast_one]
      rw [rawSum_add, ih, rawSum_one]
    rw [ih, hshift]
    push_cast
    ring

theorem rawSum_second (N : ℕ) (w : ℝ) :
    rawSum N w (fun m => (m : ℝ) ^ 2) = (N : ℝ) ^ 2 * w ^ 2 + N * w * (1 - w) := by
  induction N with
  | zero => simp [rawSum]
  | succ N ih =>
    rw [rawSum_succ]
    have hshift : rawSum N w (fun m => ((m + 1 : ℕ) : ℝ) ^ 2) =
        ((N : ℝ) ^ 2 * w ^ 2 + N * w * (1 - w)) + 2 * (N * w) + 1 := by
      have he : (fun m : ℕ => ((m + 1 : ℕ) : ℝ) ^ 2) =
          fun m : ℕ => (m : ℝ) ^ 2 + 2 * (m : ℝ) + 1 := by
        funext m
        push_cast
        ring
      rw [he, rawSum_add, rawSum_add, rawSum_const_mul, ih, rawSum_first, rawSum_one]
    rw [ih, hshift]
    push_cast
    ring

theorem rawSum_centered_second (N : ℕ) (w : ℝ) :
    rawSum N w (fun m => ((m : ℝ) - N * w) ^ 2) = N * w * (1 - w) := by
  have he : (fun m : ℕ => ((m : ℝ) - N * w) ^ 2) =
      fun m : ℕ => (m : ℝ) ^ 2 + (-2 * (N * w)) * (m : ℝ) + (N * w) ^ 2 := by
    funext m
    ring
  rw [he, rawSum_add, rawSum_add, rawSum_const_mul, rawSum_second,
    rawSum_first, rawSum_const]
  ring

lemma binomialLaw_weight (N : ℕ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (m : Fin (N + 1)) :
    (binomialLaw N w hw hw1).weight m =
      (N.choose m.val : ℝ) * (w ^ m.val * (1 - w) ^ (N - m.val)) := by
  have hnn : (⟨w, hw⟩ : ℝ≥0) ≤ 1 := by exact_mod_cast hw1
  have hen : ENNReal.ofNNReal ⟨w, hw⟩ ≤ 1 := ENNReal.coe_le_one_iff.mpr hnn
  change (PMF.binomial ⟨w, hw⟩ hnn N m).toReal = _
  rw [PMF.binomial_apply]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.coe_toReal,
    ENNReal.toReal_natCast, ENNReal.toReal_sub_of_le hen (by simp),
    ENNReal.toReal_one, NNReal.coe_mk, Fin.val_last]
  ring

lemma expectation_eq_rawSum (N : ℕ) (w : ℝ) (hw : 0 ≤ w) (hw1 : w ≤ 1)
    (f : ℕ → ℝ) :
    (binomialLaw N w hw hw1).expectation (fun m => f m.val) = rawSum N w f := by
  unfold FiniteLaw.expectation
  simp_rw [binomialLaw_weight]
  change (∑ m : Fin (N + 1),
    ((fun k : ℕ => (N.choose k : ℝ) * (w ^ k * (1 - w) ^ (N - k)) * f k) m.val)) = _
  rw [Fin.sum_univ_eq_sum_range
    (fun k : ℕ => (N.choose k : ℝ) * (w ^ k * (1 - w) ^ (N - k)) * f k) (N + 1)]
  unfold rawSum
  apply Finset.sum_congr rfl
  intro m _
  ring

/-- An actual native witness for the formerly explicit classical moment input. -/
def binomialMomentsInput : BinomialMomentsInput where
  first N w hw hw1 := by
    rw [expectation_eq_rawSum N w hw hw1 (fun m : ℕ => (m : ℝ))]
    exact rawSum_first N w
  centered_second N w hw hw1 := by
    rw [expectation_eq_rawSum N w hw hw1 (fun m : ℕ => ((m : ℝ) - N * w) ^ 2)]
    exact rawSum_centered_second N w

end Paper26.BinomialMoments
