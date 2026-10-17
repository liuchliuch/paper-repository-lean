import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Binomial identities for Lemma 2.3 (7)

The finite-population variance identity reduces to

  `C(n-1,m-1) - C(n-2,m-2) = C(n,m) · m(n-m) / (n(n-1))`,

equivalently (cleared denominators)

  `C(n,m) · m · (n-m) = C(n-1,m-1) · n · (n-1) - C(n-2,m-2) · n · (n-1)`.

We prove the two precursor identities
`C(n,m) · m = C(n-1,m-1) · n` and
`C(n,m) · m · (m-1) = C(n-2,m-2) · n · (n-1)`.
-/

noncomputable section

namespace GeometricMedianCoresets
namespace VarianceBinomial

/-- `C(n,m) · m = C(n-1,m-1) · n` for `1 ≤ m ≤ n`. -/
theorem choose_mul_eq_choose_pred (n m : ℕ) (hm : 0 < m) (hmn : m ≤ n) :
    n.choose m * m = (n - 1).choose (m - 1) * n := by
  rcases m with _ | m'
  · exact absurd hm (by simp)
  · have h1 : (m' + 1) - 1 = m' := by omega
    have hnn : n - 1 + 1 = n := by omega
    have h3 := Nat.succ_mul_choose_eq (n - 1) m'
    -- (n-1+1) * C(n-1, m') = C(n, m'+1) * (m'+1)
    rw [Nat.succ_eq_add_one, hnn] at h3
    have : n.choose (m' + 1) * (m' + 1) = (n - 1).choose m' * n := by
      nlinarith [h3]
    rw [h1]
    nlinarith [this]

/-- `C(n,m) · m · (m-1) = C(n-2,m-2) · n · (n-1)` for `2 ≤ m ≤ n`. -/
theorem choose_mul_eq_choose_pred_pred (n m : ℕ) (hm : 2 ≤ m) (hmn : m ≤ n) :
    n.choose m * (m * (m - 1)) = (n - 2).choose (m - 2) * (n * (n - 1)) := by
  have hm1 : 0 < m - 1 := by omega
  have hm2 : 0 < m := by omega
  have hmn1 : m - 1 ≤ n - 1 := by omega
  have h1 := choose_mul_eq_choose_pred n m hm2 hmn
  have h2 : (n - 1).choose (m - 1) * (m - 1)
      = (n - 2).choose (m - 2) * (n - 1) := by
    have := choose_mul_eq_choose_pred (n - 1) (m - 1) hm1 hmn1
    have hnn : n - 1 - 1 = n - 2 := by omega
    have hmm : m - 1 - 1 = m - 2 := by omega
    rw [hnn, hmm] at this
    exact this
  have h3 : n.choose m * (m * (m - 1))
      = ((n - 1).choose (m - 1) * n) * (m - 1) := by
    nlinarith [h1]
  have h4 : ((n - 1).choose (m - 1) * (m - 1)) * n
      = ((n - 2).choose (m - 2) * (n - 1)) * n := by
    nlinarith [h2]
  nlinarith [h3, h4]


end VarianceBinomial
end GeometricMedianCoresets
