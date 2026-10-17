import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Tactic
import UniformBorderRank.DiffSum
import UniformBorderRank.ProductCurve
import UniformBorderRank.FdRank

/-!
# Finite-difference limit ingredients (paper (13))

Proved here: the evaluation sequence `ε_n = ((n+1 : ℕ) : ℝ)⁻¹` is positive
and tends to `0`; each `((n+1 : ℕ) : ℂ)⁻¹` is nonzero.  These are the
analytic inputs for the `borderRankLe` assembly of paper (13).

The expansion `fdApprox = e_k + tail` and
`borderRankLe (prodCurveCoeff d v w k) (k+1)` remain **unproved**.
-/

noncomputable section

namespace UniformBorderRank

open Filter

/-- `(n+1 : ℕ) → ∞` in `ℝ`. -/
lemma tendsto_add_one_natCast :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop := by
  have h : Tendsto (fun n : ℕ => ((n : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hadd : Tendsto (fun n : ℕ => ((n : ℕ) : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ 1 h
  have heq : (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) = (fun n : ℕ => ((n : ℕ) : ℝ) + 1) := by
    funext n
    simp
  rw [heq]
  exact hadd

/-- `(n+1 : ℝ)⁻¹ → 0`. -/
lemma tendsto_inv_add_one :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (nhds 0) := by
  have h := tendsto_add_one_natCast
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero
  exact hinv.comp h

/-- Each `((n+1 : ℕ) : ℂ)⁻¹` is nonzero. -/
lemma eps_inv_ne_zero (n : ℕ) : (((n + 1 : ℕ) : ℂ)⁻¹) ≠ 0 := by
  have h : ((n + 1 : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast (by omega : (n + 1 : ℕ) ≠ 0)
  exact inv_ne_zero h

/-- `ε_n = ((n+1 : ℕ) : ℝ)⁻¹` is positive for every `n`. -/
lemma eps_inv_pos (n : ℕ) : 0 < ((n + 1 : ℕ) : ℝ)⁻¹ :=
  inv_pos.2 (by exact_mod_cast (by omega : 0 < (n + 1 : ℕ)))

end UniformBorderRank
