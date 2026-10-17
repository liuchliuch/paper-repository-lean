import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Degree computations in (1), Lemma 3.1 and Remark 2.5

The input `n * d = 2 - 2 * g` is an equality of real numbers. These lemmas
prove its numerical consequences; they do not assert the existence of a
normal bundle or a bundle isomorphism, or prove Riemann--Hurwitz.
-/
namespace Paper27.DegreeArithmetic

/-- The numerical consequence of N^⊗n ≅ TD once the geometric degree equality
has actually been established. -/
theorem normal_degree (g n d : ℝ) (hg : 2 ≤ g) (hn : 2 ≤ n)
    (hdeg : n * d = 2 - 2 * g) :
    d = -(2 * g - 2) / n ∧ d < 0 := by
  have hn₀ : n ≠ 0 := by linarith
  constructor
  · apply (eq_div_iff hn₀).mpr
    linarith
  · have hnpos : 0 < n := by linarith
    have hneg : n * d < 0 := by linarith
    by_contra hd
    have hdpos : 0 ≤ d := le_of_not_gt hd
    have hprod := mul_nonneg (le_of_lt hnpos) hdpos
    linarith

/-- The final line of Lemma 3.1 uses cancellation by the nonzero normal degree. -/
theorem common_ramification_index (d t n m : ℝ) (hd : d ≠ 0)
    (hn : n * d = t) (hm : m * d = t) : n = m := by
  exact (mul_right_cancel₀ hd) (hn.trans hm.symm)

/-- The degree of Hom(N,(f₃|D)*TB₃) is negative in Lemma 3.1. -/
theorem normal_hom_degree_negative (κ n : ℝ) (hκ : 0 < κ) (hn : 2 ≤ n) :
    -κ - (-κ / n) = -κ * (1 - 1 / n) ∧ -κ * (1 - 1 / n) < 0 := by
  have hnpos : 0 < n := by linarith
  have hlt : 1 / n < 1 := (div_lt_one hnpos).mpr (by linarith)
  constructor
  · ring
  · exact mul_neg_of_neg_of_pos (neg_neg_of_pos hκ) (by linarith)

/-- The explicit Hurwitz number in Remark 2.5. This is arithmetic, not a
formalization of the cited genus-nine covering or its ramification divisor. -/
theorem genus_nine_double_cover_ramification_number :
    (2 * (9 : ℤ) - 2) - 2 * (2 * 3 - 2) = 8 := by norm_num

end Paper27.DegreeArithmetic
