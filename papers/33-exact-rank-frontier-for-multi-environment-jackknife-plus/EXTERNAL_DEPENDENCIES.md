# External dependencies

Lean is pinned by `lean-toolchain` to `leanprover/lean4:v4.24.0`. Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` in the Lake configuration and `lake-manifest.json`; all transitive packages retain exact commit revisions in the manifest. Preserve these pins and use the repository shared tooling.

Two published results are explicit theorem parameters, with no added local axioms and no supplied Lean inhabitants:

- `MEJF.RankDP.LandauInput` (`MEJF/RankDP.lean`) is the Landau tournament score characterization. For each descending list of natural numbers it equates existence of an actual tournament with the full length, entry, total-sum and reversed-prefix inequalities. It is used only by `eval_eq_maxObjective` and `dp_computes_gamma`, identifying the proved DP with the tournament/statistical value. The statistical minimax law, common learner, recurrence, state correctness and operation counts are proved locally. Reference: H. G. Landau (1953), [DOI](https://doi.org/10.1007/BF02476378).
- `MEJF.HeterogeneousSortingInput.PublishedMergeSortContract` is an optional supplied sorter: one sorter and one positive constant work uniformly for every indexed natural input; the output is monotone, preserves occurrences through an actual permutation, and costs at most `C*N*(Nat.clog 2 N+1)` operations. It is used only by the optional full sorting pipeline. The Hall/cut reduction, frontier and after-sorting quadratic algorithm are local proofs. Reference: Sedgewick–Wayne, *Algorithms*, fourth edition, [section 2.2](https://algs4.cs.princeton.edu/22mergesort/index.php); the uniform RAM contract is an explicit implementation interpretation, not a supplied Lean mergesort proof.

Hall's theorem comes from pinned Mathlib. The specialized incidence realization, tie removal and total-variation swap arguments are proved locally. No external certificate/data assets are required.

Official Comparator uses the repository shared pinned installation. Challenge modules intentionally contain proof placeholders to specify fixed expected theorem types. They and deliberate negative-control axioms are verification fixtures, outside the production build target. The production proof closure must be checked independently of those fixtures.
