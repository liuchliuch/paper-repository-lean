import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# Further counting engines (Proposition 10)

Local pruning survival probability: for `k ∈ {3,4}` and `d ≤ 2` the fraction
of two-subsets containing a fixed `d`-subset is `binom(k-d, 2-d) / binom(k,2)`,
and this is at least `1/6`.
-/

open Finset

namespace K44K35Free

/-- For `k ∈ {3,4}` and `d ≤ 2` the number of two-subsets of a `k`-set that
contain a fixed `d`-subset is `binom(k-d, 2-d)`, and
`6 * binom(k-d, 2-d) ≥ binom(k,2)`. -/
theorem prune_survival_prob (k d : ℕ)
    (hk : k = 3 ∨ k = 4) (hd : d ≤ 2) (hdk : d ≤ k) :
    (k - d).choose (2 - d) * 6 ≥ (k.choose 2) := by
  rcases hk with hk | hk <;> subst hk
  · -- k = 3; d ∈ {0,1,2}
    have : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num [Nat.choose]
  · -- k = 4; d ∈ {0,1,2}
    have : d = 0 ∨ d = 1 ∨ d = 2 := by omega
    rcases this with rfl | rfl | rfl <;> norm_num [Nat.choose]

/-- Explicit form of the probability `binom(k-d, 2-d) / binom(k,2) ≥ 1/6`. -/
theorem prune_survival_prob_rat (k d : ℕ)
    (hk : k = 3 ∨ k = 4) (hd : d ≤ 2) (hdk : d ≤ k) :
    (1 / 6 : ℚ) ≤ ((k - d).choose (2 - d) : ℚ) / (k.choose 2) := by
  have h2 : 2 ≤ k := by rcases hk with rfl | rfl <;> norm_num [Nat.choose]
  have hpos : 0 < (k.choose 2 : ℚ) := by
    rw [Nat.cast_pos]
    exact Nat.choose_pos h2
  have h := prune_survival_prob k d hk hd hdk
  have h' : ((k - d).choose (2 - d) : ℚ) * 6 ≥ (k.choose 2 : ℚ) := by
    exact_mod_cast h
  apply (le_div_iff₀ hpos).mpr
  norm_num
  nlinarith

/-- Proposition 10 probability product is strictly positive. -/
theorem prune_product_bound (L : ℕ) :
    (0 : ℝ) < 1 / 6 ^ (16 * L) := by
  positivity

end K44K35Free
