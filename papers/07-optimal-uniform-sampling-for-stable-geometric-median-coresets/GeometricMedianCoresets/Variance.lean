import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Algebra.Module.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Combinatorial preparation for Lemma 2.3

Closed counting facts about `m`-element subsets and centered families.
The full finite-population variance identity (7) is proved in
`GeometricMedianCoresets.VarianceComplete`.
-/

noncomputable section

open scoped BigOperators

namespace GeometricMedianCoresets
namespace FinitePopulation

theorem card_powersetCard (n m : ℕ) :
    ((Finset.univ : Finset (Fin n)).powersetCard m).card = n.choose m := by
  simp [Finset.card_powersetCard]

/-- When `m = n` the only subset is the full set. -/
theorem powersetCard_self (n : ℕ) :
    (Finset.univ : Finset (Fin n)).powersetCard n = {Finset.univ} := by
  ext s
  simp only [Finset.mem_powersetCard, Finset.mem_singleton, Finset.subset_univ,
    true_and]
  constructor
  · intro h
    have hcard : s.card = Fintype.card (Fin n) := by
      simpa using h
    exact (Finset.card_eq_iff_eq_univ s).1 hcard
  · intro h
    subst h
    simp

/-- When `m = n` the uniform sum is evaluation at the full set. -/
theorem sum_powersetCard_self {n : ℕ} (hn : 0 < n) (f : (Finset (Fin n)) → ℝ) :
    (∑ s ∈ (Finset.univ : Finset (Fin n)).powersetCard n, f s) = f Finset.univ := by
  rw [powersetCard_self, Finset.sum_singleton]

end FinitePopulation
end GeometricMedianCoresets
