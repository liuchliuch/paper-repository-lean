# Boundary reduction for growth-optimal e-variables: a Gaussian theorem and a finite counterexample

[Source paper](https://liuchliuch.github.io/repository/boundary-reduction-for-growth-optimal-e-variables-a-gaussian-theorem-and-a-finite-counterexample/).

Lean formalization of Gaussian boundary reduction, finite exponential-family obstructions, and the explicit nine-point counterexample. The production entry is `BoundaryReduction.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Lemma 2.1 | `BoundaryReduction.NEF.lemma_2_1` | GROW–information bound for arbitrary subfamilies of tilted laws on an open exponential-moment domain; the extended logarithm permits zero e-variables. |
| Theorem 3.1 | `BoundaryReduction.NinePoint.theorem_3_1_mean` | Explicit minimal nine-point model, compact mean-space excluded ball, strict information gap, and obstruction for every Borel boundary prior. |
| Proposition 3.2 | `BoundaryReduction.FiniteExponential.proposition_3_2_full` | Exposed-vertex information bounds and Borel obstruction for finite positive minimal exponential families with the stated mean-image containment. |
| Theorem 4.1 | `BoundaryReduction.Gaussian.theorem_4_1_covariance` | Full boundary conclusion for a centered Gaussian with symmetric positive definite covariance and a bounded open neighborhood of zero in positive dimension; the inverse precision operator is constructed. |
| Proposition 4.2 | `BoundaryReduction.Gaussian.proposition_4_2_iff` | Borel variational optimality equivalence; `proposition_4_2_gap` proves the computable gap bound. |
| Lemma 4.3 | `BoundaryReduction.first_exit_propagation` | Raywise-convex first-exit propagation for arbitrary open neighborhoods of zero. |
| Corollary 4.4 | `BoundaryReduction.Gaussian.corollary_4_4_family` | Finite priors on optimal support, exact KL identity, quadratic error, and weak convergence; `corollary_4_4_map` supplies the map bound. |
| Lemma A.1; displays A.5–A.12 | `BoundaryReduction.NinePoint.lemma_A_1` | Exterior component means and the explicit KL bound at t = 200; `Verification.appendix_closed_forms` states the exact appendix formulas. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 01 --check static
python3 ../../scripts/verify.py --paper 01 --check build
python3 ../../scripts/verify.py --paper 01 --check comparator --suite main
```

## Assumptions

The main results use no additional paper-specific theorem axiom. Mean-image containment, identifiability, and the required Borel inverses are proved within the development. See [External dependencies](EXTERNAL_DEPENDENCIES.md) for the mathematical boundary and pinned libraries.

## Verification

The main contracts include the general NEF, actual Gaussian covariance, mean-space counterexample, and appendix statements. Challenge placeholders and deliberately invalid premise/axiom controls are isolated from the production entry. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/boundary-reduction-for-growth-optimal-e-variables-a-gaussian-theorem-and-a-finite-counterexample/).
