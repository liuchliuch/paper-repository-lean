import Paper29.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NthRewrite

/-! The explicit one-dimensional instances of Proposition 5.1 and Appendix B.
`N` is a real multiplicity parameter; the theorems apply in particular to every
integer number of repeated rows with `N ≥ 1`. -/
noncomputable section
open scoped BigOperators

namespace Paper29.Surrogates

private theorem sqrt_four : Real.sqrt (4 : ℝ) = 2 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]

/-- A supporting affine function of the width-one Huber loss. -/
theorem supporting_line (s t : ℝ) (hs : |s| ≤ 1) :
    s * t - s ^ 2 / 2 ≤ huber t := by
  have hs' := abs_le.mp hs
  unfold huber
  split_ifs with ht
  · nlinarith [sq_nonneg (t - s)]
  · by_cases hpos : 0 ≤ t
    · rw [abs_of_nonneg hpos] at *
      have ht' : 1 < t := lt_of_not_ge ht
      nlinarith [mul_nonneg (sub_nonneg.mpr hs'.2) (le_of_lt (sub_pos.mpr ht')),
        sq_nonneg (s - 1)]
    · rw [abs_of_neg (lt_of_not_ge hpos)] at *
      have ht' : t < -1 := by linarith
      nlinarith [mul_nonneg (by linarith : 0 ≤ 1 + s)
          (by linarith : 0 ≤ -t - 1), sq_nonneg (s + 1)]

def leastSquares (N x : ℝ) : ℝ := N * x ^ 2 + N * (x - 4) ^ 2

def leastSquaresHuber (N x : ℝ) : ℝ :=
  N * huber x + huber (Real.sqrt N * (x - 4))

def absoluteLoss (N x : ℝ) : ℝ := N * |x| + |N * x / 2 - 1|

def absoluteHuber (N x : ℝ) : ℝ :=
  N * huber x + huber (N * x / 2 - 1)

theorem leastSquares_unique_minimizer (N : ℝ) (hN : 0 < N) :
    (∀ x, leastSquares N 2 ≤ leastSquares N x) ∧
      (∀ x, leastSquares N x = leastSquares N 2 ↔ x = 2) := by
  have hid (x : ℝ) : leastSquares N x = leastSquares N 2 + 2 * N * (x - 2) ^ 2 := by
    unfold leastSquares
    ring
  constructor
  · intro x
    rw [hid x]
    nlinarith [sq_nonneg (x - 2)]
  · intro x
    rw [hid x]
    constructor
    · intro h
      have : (x - 2) ^ 2 = 0 := by nlinarith [sq_nonneg (x - 2)]
      exact sub_eq_zero.mp (sq_eq_zero_iff.mp this)
    · rintro rfl
      ring

private theorem sqrt_facts (N : ℝ) (hN : 1 ≤ N) :
    1 ≤ Real.sqrt N ∧ 0 < Real.sqrt N ∧ (Real.sqrt N) ^ 2 = N := by
  have h0 : 0 ≤ N := by linarith
  have hsq := Real.sq_sqrt h0
  have hs := Real.sqrt_nonneg N
  have hge : 1 ≤ Real.sqrt N := Real.one_le_sqrt.mpr hN
  exact ⟨hge, by linarith, hsq⟩

theorem leastSquaresHuber_optimum_value (N : ℝ) (hN : 1 ≤ N) :
    leastSquaresHuber N (1 / Real.sqrt N) = 4 * Real.sqrt N - 1 := by
  obtain ⟨hs, hs0, hsq⟩ := sqrt_facts N hN
  have hnz := ne_of_gt hs0
  have hinv0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have hinv1 : 1 / Real.sqrt N ≤ 1 := (div_le_one hs0).2 hs
  have hx : |1 / Real.sqrt N| ≤ 1 := abs_le.mpr ⟨by linarith, hinv1⟩
  have hres : Real.sqrt N * (1 / Real.sqrt N - 4) = 1 - 4 * Real.sqrt N := by
    field_simp
    <;> ring
  have htail : ¬ |1 - 4 * Real.sqrt N| ≤ 1 := by
    rw [abs_of_neg (by linarith : 1 - 4 * Real.sqrt N < 0)]
    linarith
  unfold leastSquaresHuber huber
  rw [if_pos hx, hres, if_neg htail,
    abs_of_neg (by linarith : 1 - 4 * Real.sqrt N < 0)]
  nth_rw 1 [← hsq]
  field_simp
  <;> ring

theorem leastSquaresHuber_minimizer (N : ℝ) (hN : 1 ≤ N) (x : ℝ) :
    leastSquaresHuber N (1 / Real.sqrt N) ≤ leastSquaresHuber N x := by
  obtain ⟨hs, hs0, hsq⟩ := sqrt_facts N hN
  have hnz := ne_of_gt hs0
  have hinv0 : 0 ≤ 1 / Real.sqrt N := by positivity
  have hinv1 : 1 / Real.sqrt N ≤ 1 := (div_le_one hs0).2 hs
  have h1 := supporting_line (1 / Real.sqrt N) x
    (abs_le.mpr ⟨by linarith, hinv1⟩)
  have h2 := supporting_line (-1) (Real.sqrt N * (x - 4)) (by norm_num)
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ N)
  rw [leastSquaresHuber_optimum_value N hN]
  unfold leastSquaresHuber
  have hc : N * (1 / Real.sqrt N * x - (1 / Real.sqrt N) ^ 2 / 2) +
      (-1 * (Real.sqrt N * (x - 4)) - (-1 : ℝ) ^ 2 / 2) =
        4 * Real.sqrt N - 1 := by
    nth_rw 1 [← hsq]
    field_simp
    <;> ring
  linarith

theorem leastSquaresHuber_surrogate_value (N : ℝ) (hN : 1 ≤ N) :
    leastSquaresHuber N 2 = 3 / 2 * N + 2 * Real.sqrt N - 1 / 2 := by
  obtain ⟨hs, hs0, hsq⟩ := sqrt_facts N hN
  have hh2 : huber (2 : ℝ) = 3 / 2 := by norm_num [huber]
  have ht : Real.sqrt N * (2 - 4) < 0 := by nlinarith
  have htail : huber (Real.sqrt N * (2 - 4)) = 2 * Real.sqrt N - 1 / 2 := by
    unfold huber
    rw [abs_of_neg ht, if_neg (by nlinarith : ¬ -(Real.sqrt N * (2 - 4)) ≤ 1)]
    ring
  unfold leastSquaresHuber
  rw [hh2, htail]
  ring

/-- Explicit constant bounds proving the squared approximation ratio grows
linearly in `√N`, and hence its square root grows as `N^(1/4)`. -/
theorem leastSquaresHuber_ratio_bounds (N : ℝ) (hN : 1 ≤ N) :
    Real.sqrt N / 4 ≤
      leastSquaresHuber N 2 / leastSquaresHuber N (1 / Real.sqrt N) ∧
    leastSquaresHuber N 2 / leastSquaresHuber N (1 / Real.sqrt N) ≤ Real.sqrt N := by
  obtain ⟨hs, hs0, hsq⟩ := sqrt_facts N hN
  rw [leastSquaresHuber_surrogate_value N hN, leastSquaresHuber_optimum_value N hN]
  have hd : 0 < 4 * Real.sqrt N - 1 := by linarith
  constructor
  · apply (le_div_iff₀ hd).2
    nlinarith
  · apply (div_le_iff₀ hd).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hs)
      (by linarith : 0 ≤ 5 * Real.sqrt N - 1)]

/-- Bounds on the actual Huber-norm approximation ratio, with absolute
constants, valid for every `N ≥ 1`. -/
theorem leastSquaresHuber_norm_ratio_bounds (N : ℝ) (hN : 1 ≤ N) :
    Real.sqrt (Real.sqrt N) / 2 ≤
      Real.sqrt (leastSquaresHuber N 2) /
        Real.sqrt (leastSquaresHuber N (1 / Real.sqrt N)) ∧
    Real.sqrt (leastSquaresHuber N 2) /
        Real.sqrt (leastSquaresHuber N (1 / Real.sqrt N)) ≤
      Real.sqrt (Real.sqrt N) := by
  have hnum : 0 ≤ leastSquaresHuber N 2 := by
    rw [leastSquaresHuber_surrogate_value N hN]
    obtain ⟨hs, hs0, hsq⟩ := sqrt_facts N hN
    nlinarith
  rw [← Real.sqrt_div hnum]
  obtain ⟨hlo, hhi⟩ := leastSquaresHuber_ratio_bounds N hN
  constructor
  · have h := Real.sqrt_le_sqrt hlo
    simpa [Real.sqrt_div (Real.sqrt_nonneg N), sqrt_four] using h
  · exact Real.sqrt_le_sqrt hhi

theorem absoluteLoss_unique_minimizer (N : ℝ) (hN : 0 < N) :
    (∀ x, absoluteLoss N 0 ≤ absoluteLoss N x) ∧
      (∀ x, absoluteLoss N x = absoluteLoss N 0 ↔ x = 0) := by
  have hlower (x : ℝ) : 1 + N / 2 * |x| ≤ absoluteLoss N x := by
    unfold absoluteLoss
    by_cases hx : 0 ≤ x
    · rw [abs_of_nonneg hx]
      nlinarith [neg_le_abs (N * x / 2 - 1)]
    · rw [abs_of_neg (lt_of_not_ge hx)]
      have hres : N * x / 2 - 1 < 0 := by nlinarith
      rw [abs_of_neg hres]
      nlinarith
  have hzero : absoluteLoss N 0 = 1 := by norm_num [absoluteLoss]
  constructor
  · intro x
    rw [hzero]
    have := hlower x
    nlinarith [abs_nonneg x]
  · intro x
    constructor
    · intro h
      rw [hzero] at h
      have := hlower x
      have : |x| = 0 := by nlinarith [abs_nonneg x]
      exact abs_eq_zero.mp this
    · rintro rfl
      rfl

private theorem absolute_residual_facts (N : ℝ) (hN : 1 ≤ N) :
    |2 / (N + 4)| ≤ 1 ∧ |-4 / (N + 4)| ≤ 1 ∧
    N * (2 / (N + 4)) / 2 - 1 = -4 / (N + 4) := by
  have hd : 0 < N + 4 := by linarith
  constructor
  · rw [abs_of_nonneg (by positivity : 0 ≤ 2 / (N + 4))]
    apply (div_le_one hd).2
    linarith
  constructor
  · rw [abs_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by norm_num) (le_of_lt hd) : -4 / (N + 4) ≤ 0)]
    rw [neg_div, neg_neg]
    apply (div_le_one hd).2
    linarith
  · field_simp
    <;> ring

theorem absoluteHuber_optimum_value (N : ℝ) (hN : 1 ≤ N) :
    absoluteHuber N (2 / (N + 4)) = 2 / (N + 4) := by
  obtain ⟨hx, hr, heq⟩ := absolute_residual_facts N hN
  have hd : N + 4 ≠ 0 := by linarith
  unfold absoluteHuber
  rw [heq]
  simp only [huber, if_pos hx, if_pos hr]
  field_simp
  <;> ring

theorem absoluteHuber_minimizer (N : ℝ) (hN : 1 ≤ N) (x : ℝ) :
    absoluteHuber N (2 / (N + 4)) ≤ absoluteHuber N x := by
  obtain ⟨hx, hr, heq⟩ := absolute_residual_facts N hN
  have hd : N + 4 ≠ 0 := by linarith
  have h1 := supporting_line (2 / (N + 4)) x hx
  have h2 := supporting_line (-4 / (N + 4)) (N * x / 2 - 1) hr
  have h1' := mul_le_mul_of_nonneg_left h1 (by linarith : 0 ≤ N)
  rw [absoluteHuber_optimum_value N hN]
  unfold absoluteHuber
  have hc : N * (2 / (N + 4) * x - (2 / (N + 4)) ^ 2 / 2) +
      (-4 / (N + 4) * (N * x / 2 - 1) - (-4 / (N + 4)) ^ 2 / 2) =
        2 / (N + 4) := by
    field_simp
    <;> ring
  linarith

theorem absoluteHuber_surrogate_value (N : ℝ) : absoluteHuber N 0 = 1 / 2 := by
  norm_num [absoluteHuber, huber]

theorem absoluteHuber_ratio_exact (N : ℝ) (hN : 1 ≤ N) :
    absoluteHuber N 0 / absoluteHuber N (2 / (N + 4)) = (N + 4) / 4 := by
  rw [absoluteHuber_surrogate_value, absoluteHuber_optimum_value N hN]
  have hd : N + 4 ≠ 0 := by linarith
  field_simp
  <;> ring

/-- The square-root objectives give precisely the ratio stated in Appendix B. -/
theorem absoluteHuber_norm_ratio_exact (N : ℝ) (hN : 1 ≤ N) :
    Real.sqrt (absoluteHuber N 0) / Real.sqrt (absoluteHuber N (2 / (N + 4))) =
      Real.sqrt ((N + 4) / 4) := by
  rw [← Real.sqrt_div (by norm_num [absoluteHuber_surrogate_value] :
    0 ≤ absoluteHuber N 0), absoluteHuber_ratio_exact N hN]

/-- Explicit constants for the `Θ(√N)` claim. -/
theorem absoluteHuber_norm_ratio_bounds (N : ℝ) (hN : 1 ≤ N) :
    Real.sqrt N / 2 ≤
      Real.sqrt (absoluteHuber N 0) / Real.sqrt (absoluteHuber N (2 / (N + 4))) ∧
    Real.sqrt (absoluteHuber N 0) / Real.sqrt (absoluteHuber N (2 / (N + 4))) ≤
      2 * Real.sqrt N := by
  rw [absoluteHuber_norm_ratio_exact N hN]
  constructor
  · have h := Real.sqrt_le_sqrt (show N / 4 ≤ (N + 4) / 4 by linarith)
    simpa [Real.sqrt_div (by linarith : 0 ≤ N), sqrt_four] using h
  · have h := Real.sqrt_le_sqrt (show (N + 4) / 4 ≤ 4 * N by linarith)
    simpa [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), sqrt_four] using h

/-- An explicit finite row list with `N` copies of `(1,0)` and one exceptional
row `(a,b)`, so the scalar formulas above are genuine finite data instances. -/
def repeatedHuber (N : ℕ) (a b x : ℝ) : ℝ :=
  ∑ i : Fin (N + 1), huber ((if i.val < N then 1 else a) * x -
    (if i.val < N then 0 else b))

theorem repeatedHuber_eq (N : ℕ) (a b x : ℝ) :
    repeatedHuber N a b x = (N : ℝ) * huber x + huber (a * x - b) := by
  unfold repeatedHuber
  rw [Fin.sum_univ_castSucc]
  simp

theorem leastSquaresHuber_finite_instance (N : ℕ) (x : ℝ) :
    repeatedHuber N (Real.sqrt N) (4 * Real.sqrt N) x = leastSquaresHuber N x := by
  rw [repeatedHuber_eq]
  unfold leastSquaresHuber
  congr 2
  ring

theorem absoluteHuber_finite_instance (N : ℕ) (x : ℝ) :
    repeatedHuber N ((N : ℝ) / 2) 1 x = absoluteHuber N x := by
  rw [repeatedHuber_eq]
  unfold absoluteHuber
  congr 2
  ring

/-- The feature matrix and labels of the repeated-row construction. -/
def rowDesign (N : ℕ) (a : ℝ) : Matrix (Fin (N + 1)) (Fin 1) ℝ :=
  fun i _ => if i.val < N then 1 else a

def rowResponse (N : ℕ) (b : ℝ) : Fin (N + 1) → ℝ :=
  fun i => if i.val < N then 0 else b

theorem repeatedHuber_objective (N : ℕ) (a b x : ℝ) :
    objective (rowDesign N a) (rowResponse N b) (fun _ => x) = repeatedHuber N a b x := by
  simp [objective, rowDesign, rowResponse, repeatedHuber, Matrix.mulVec, dotProduct]

theorem leastSquares_finite_surrogate (N : ℕ) (x : ℝ) :
    (∑ i : Fin (N + 1),
      (((rowDesign N (Real.sqrt N)).mulVec (fun _ => x)) i -
        rowResponse N (4 * Real.sqrt N) i) ^ 2) = leastSquares N x := by
  simp only [Matrix.mulVec, dotProduct, rowDesign, rowResponse]
  simp only [Fin.sum_univ_one]
  rw [Fin.sum_univ_castSucc]
  simp
  unfold leastSquares
  congr 1
  calc
    (Real.sqrt (N : ℝ) * x - 4 * Real.sqrt N) ^ 2 =
        (Real.sqrt N) ^ 2 * (x - 4) ^ 2 := by ring
    _ = (N : ℝ) * (x - 4) ^ 2 := by rw [Real.sq_sqrt (Nat.cast_nonneg N)]

theorem absoluteLoss_finite_surrogate (N : ℕ) (x : ℝ) :
    (∑ i : Fin (N + 1),
      |((rowDesign N ((N : ℝ) / 2)).mulVec (fun _ => x)) i - rowResponse N 1 i|) =
        absoluteLoss N x := by
  simp only [Matrix.mulVec, dotProduct, rowDesign, rowResponse]
  simp only [Fin.sum_univ_one]
  rw [Fin.sum_univ_castSucc]
  simp
  unfold absoluteLoss
  congr 2
  ring

end Paper29.Surrogates
