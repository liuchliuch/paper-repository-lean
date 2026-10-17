import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Finite classical parts of Section 1.2 and Appendix C. These are the losses
of commuting density matrices. This module does not assert the quantum
measurement maximization in Lemma 1.4.
-/
noncomputable section
open scoped BigOperators

namespace Paper26.Classical

variable {ι : Type*} [Fintype ι]

def chiSquared (p q : ι → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2 / q i

def frobeniusSquared (p q : ι → ℝ) : ℝ := ∑ i, (p i - q i) ^ 2

def hellingerSquared (p q : ι → ℝ) : ℝ :=
  ∑ i, (Real.sqrt (p i) - Real.sqrt (q i)) ^ 2

def traceNorm (p q : ι → ℝ) : ℝ := ∑ i, |p i - q i|

def IsDistribution (p : ι → ℝ) : Prop :=
  (∀ i, 0 ≤ p i) ∧ ∑ i, p i = 1

theorem chiSquared_nonneg (p q : ι → ℝ) (hq : ∀ i, 0 ≤ q i) :
    0 ≤ chiSquared p q := by
  exact Finset.sum_nonneg fun i _ => div_nonneg (sq_nonneg _) (hq i)

theorem traceNorm_sq_le_chiSquared (p q : ι → ℝ)
    (hq : ∀ i, 0 < q i) (hsum : ∑ i, q i = 1) :
    traceNorm p q ^ 2 ≤ chiSquared p q := by
  have h := Finset.sq_sum_div_le_sum_sq_div Finset.univ
    (fun i => |p i - q i|) (fun i _ => hq i)
  simpa [traceNorm, chiSquared, hsum, sq_abs] using h

theorem sqrt_sub_sq_le_chiSquared_term {p q : ℝ}
    (hp : 0 ≤ p) (hq : 0 < q) :
    (Real.sqrt p - Real.sqrt q) ^ 2 ≤ (p - q) ^ 2 / q := by
  apply (le_div_iff₀ hq).2
  have hx := Real.sqrt_nonneg p
  have hy := Real.sqrt_nonneg q
  have hx2 := Real.sq_sqrt hp
  have hy2 := Real.sq_sqrt hq.le
  have h := mul_nonneg (sq_nonneg (Real.sqrt p - Real.sqrt q))
    (show 0 ≤ Real.sqrt p ^ 2 + 2 * Real.sqrt p * Real.sqrt q by positivity)
  nlinarith

theorem hellingerSquared_le_chiSquared (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) :
    hellingerSquared p q ≤ chiSquared p q := by
  exact Finset.sum_le_sum fun i _ => sqrt_sub_sq_le_chiSquared_term (hp i) (hq i)

theorem chiSquared_expansion (p q : ι → ℝ)
    (hq : ∀ i, q i ≠ 0) :
    chiSquared p q = (∑ i, p i ^ 2 / q i) - 2 * (∑ i, p i) + ∑ i, q i := by
  unfold chiSquared
  calc
    _ = ∑ i, (p i ^ 2 / q i - 2 * p i + q i) := by
      apply Finset.sum_congr rfl
      intro i _
      field_simp [hq i]
      ring
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]

theorem chiSquared_of_distributions (p q : ι → ℝ)
    (hp : IsDistribution p) (hq : IsDistribution q) (hqpos : ∀ i, 0 < q i) :
    chiSquared p q = (∑ i, p i ^ 2 / q i) - 1 := by
  rw [chiSquared_expansion p q (fun i => ne_of_gt (hqpos i)), hp.2, hq.2]
  ring

def counterexampleInput (b q : ℝ) : Fin 2 → ℝ := ![q + b, 1 - q - b]
def counterexampleEstimate (q : ℝ) : Fin 2 → ℝ := ![q, 1 - q]

theorem counterexampleInput_distribution {b q : ℝ}
    (hb : 0 < b) (hq : 0 < q) (hqb : q < 1 - b) :
    IsDistribution (counterexampleInput b q) := by
  constructor
  · intro i
    fin_cases i <;> simp [counterexampleInput] <;> linarith
  · simp [counterexampleInput, Fin.sum_univ_two]

theorem counterexampleEstimate_distribution {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    IsDistribution (counterexampleEstimate q) := by
  constructor
  · intro i
    fin_cases i <;> simp [counterexampleEstimate] <;> linarith
  · simp [counterexampleEstimate, Fin.sum_univ_two]

/-- Exact Frobenius formula (55), without limits or asymptotic placeholders. -/
theorem counterexample_frobenius (b q : ℝ) :
    frobeniusSquared (counterexampleInput b q) (counterexampleEstimate q) = 2 * b ^ 2 := by
  simp [frobeniusSquared, counterexampleInput, counterexampleEstimate, Fin.sum_univ_two]
  ring

/-- Exact commuting chi-squared formula (55). -/
theorem counterexample_chiSquared (b q : ℝ) :
    chiSquared (counterexampleInput b q) (counterexampleEstimate q) =
      b ^ 2 * (1 / q + 1 / (1 - q)) := by
  simp [chiSquared, counterexampleInput, counterexampleEstimate, Fin.sum_univ_two]
  ring

/-- For a fixed Frobenius error of 1/8, the loss exceeds every proposed bound.
The witnesses are strictly positive probability vectors from Appendix C. -/
theorem no_uniform_frobenius_control (M : ℝ) :
    ∃ q : ℝ, 0 < q ∧ q < 3 / 4 ∧
      IsDistribution (counterexampleInput (1 / 4) q) ∧
      IsDistribution (counterexampleEstimate q) ∧
      frobeniusSquared (counterexampleInput (1 / 4) q) (counterexampleEstimate q) = 1 / 8 ∧
      M < chiSquared (counterexampleInput (1 / 4) q) (counterexampleEstimate q) := by
  let q : ℝ := 1 / (16 * (|M| + 1))
  have hm : 0 < |M| + 1 := by positivity
  have hq : 0 < q := by dsimp [q]; positivity
  have hqsmall : q ≤ 1 / 16 := by
    dsimp [q]
    apply (div_le_div_iff₀ (by positivity) (by norm_num)).2
    nlinarith [abs_nonneg M]
  have hq1 : q < 1 := by linarith
  have hq34 : q < 3 / 4 := by linarith
  refine ⟨q, hq, hq34,
    counterexampleInput_distribution (by norm_num) hq (by linarith),
    counterexampleEstimate_distribution hq hq1, ?_, ?_⟩
  · rw [counterexample_frobenius]
    norm_num
  · rw [counterexample_chiSquared]
    have hident : (1 / 4 : ℝ) ^ 2 * (1 / q) = |M| + 1 := by
      dsimp [q]
      field_simp
      ring
    have htail : 0 ≤ (1 / 4 : ℝ) ^ 2 * (1 / (1 - q)) :=
      mul_nonneg (sq_nonneg _) (div_nonneg (by norm_num) (by linarith))
    have hM : M < |M| + 1 := by linarith [le_abs_self M]
    nlinarith

end Paper26.Classical
