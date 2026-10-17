import MEJF.HeterogeneousAlgorithm
import Mathlib.Data.Nat.Log

/-! # Optional published sorting input for the heterogeneous algorithm

This module does not assert or prove the existence of a sorter. It specifies an
explicit external input for classical mergesort correctness and its uniform
O(N log N) RAM cost, then proves composition with our fully proved frontier
program. No graph-feasibility or frontier step is an external input.

Published references: D. E. Knuth, The Art of Computer Programming, Vol. 3,
Sorting and Searching, 2nd ed. (1998), §5.2.4; R. Sedgewick and K. Wayne,
Algorithms, 4th ed. (2011), §2.2, with author-maintained presentation at
https://algs4.cs.princeton.edu/22mergesort/index.php . The latter states the
worst-case N log N comparison/time guarantee and linear auxiliary storage.
The uniform constant below permits counting every RAM primitive, not just key
comparisons. Its existence is explicitly left as the published external input.
-/
namespace MEJF.HeterogeneousSortingInput

open MEJF.HeterogeneousAlgorithm MEJF.HeterogeneousFrontier

/-- Exact shape of the optional known external sorting theorem. A single
constant works for every finite natural-valued input, and the output preserves
indexed occurrences through an actual permutation, including repeated values. -/
structure PublishedMergeSortContract where
  sorter : (N : ℕ) → (Fin N → ℕ) → Computation (Fin N → ℕ)
  output_monotone : ∀ N w, Monotone (sorter N w).value
  output_permutation : ∀ N w, ∃ σ : Equiv.Perm (Fin N), (sorter N w).value = w ∘ σ
  uniformConstant : ℕ
  positiveConstant : 0 < uniformConstant
  unitCost_bound : ∀ N w, (sorter N w).ops ≤ uniformConstant*N*(Nat.clog 2 N+1)

/-- Optional full pipeline. Sorting is the explicit supplied program; every
frontier constraint and the final maximum are evaluated by our own program. -/
def computeWithSorter (published : PublishedMergeSortContract) {N : ℕ} (w : Fin N → ℕ) :
    Computation ℕ :=
  Computation.seq (published.sorter N w) computeAfterSorting

/-- Sorting correctness alone suffices to connect the full pipeline to the
original s*, with no externally assumed feasibility computation. -/
theorem computeWithSorter_correct (published : PublishedMergeSortContract) {N : ℕ} (w : Fin N → ℕ) :
    (computeWithSorter published w).value = sStar w := by
  obtain ⟨σ,hσ⟩ := published.output_permutation N w
  change (computeAfterSorting (published.sorter N w).value).value = sStar w
  rw [(sortedInput_correct _ (published.output_monotone N w)).1,hσ,sStar_perm]

theorem computeWithSorter_maximumSupported (published : PublishedMergeSortContract)
    {N : ℕ} (w : Fin N → ℕ) :
    (computeWithSorter published w).value = maximumSupported w := by
  rw [computeWithSorter_correct,maximumSupported_eq_sStar]

/-- The exact unproved external sort cost is exposed, while the subsequent
cost is the proved recursive program count. -/
theorem computeWithSorter_ops (published : PublishedMergeSortContract) {N : ℕ} (w : Fin N → ℕ) :
    (computeWithSorter published w).ops = (published.sorter N w).ops+7*N*N+16*N := by
  unfold computeWithSorter Computation.seq
  rw [computeAfterSorting_ops]
  change (published.sorter N w).ops+(7*N*N+16*N) = (published.sorter N w).ops+7*N*N+16*N
  omega

/-- Composition with any supplied correct sorter gives the actual frontier
with at most its own charged cost plus 23N² proven frontier operations. -/
theorem computeWithSorter_ops_le (published : PublishedMergeSortContract) {N : ℕ}
    (w : Fin N → ℕ) (hN : 1 ≤ N) :
    (computeWithSorter published w).ops ≤ (published.sorter N w).ops+23*N^2 := by
  change (published.sorter N w).ops + (computeAfterSorting (published.sorter N w).value).ops ≤ _
  exact Nat.add_le_add_left (computeAfterSorting_ops_le _ hN) _

/-- The final bound keeps the precise, uniform external sorting hypothesis
visible rather than silently replacing it by a proved implementation. -/
theorem computeWithSorter_uniform_bound (published : PublishedMergeSortContract) {N : ℕ}
    (w : Fin N → ℕ) (hN : 1 ≤ N) :
    (computeWithSorter published w).ops ≤
      published.uniformConstant*N*(Nat.clog 2 N+1)+23*N^2 := by
  apply (computeWithSorter_ops_le published w hN).trans
  exact Nat.add_le_add_right (published.unitCost_bound N w) _

end MEJF.HeterogeneousSortingInput
