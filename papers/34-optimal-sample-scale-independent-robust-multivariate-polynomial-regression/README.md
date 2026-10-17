# Scale-Independent Robust Multivariate Polynomial Regression

Source: [paper](https://liuchliuch.github.io/repository/optimal-sample-scale-independent-robust-multivariate-polynomial-regression/).

## Results

The entry module is `Paper34.lean`. The estimator uses native multivariate polynomials and takes neither the unknown truth, noise level nor hidden outlier flags as inputs.

| Source result | Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1, Chebyshev design | `Paper34.theorem_1_1_chebyshev` | Fixed-budget estimator, recovery probability and scale-independent bounds for iid locations and independent label outliers. |
| Theorem 1.1, uniform design | `Paper34.theorem_1_1_uniform` | Uniform-cube recovery with explicit grid/sample ceilings and iteration budget. |
| Computational bound | `Paper34.source_outside_finite_loop_polynomial` | LP encodings, call counts and polynomial outside-loop arithmetic in an exact-real LP-oracle model. |
| Appendix A, total-degree restriction | `Paper34.AppendixSpaces.restricted_source_chebyshev` | Actual restricted estimator and its probability rates. Other modules cover degree zero, other designs and anisotropic degrees. |

Tensor norming, arbitrary joint cell representatives, LAD initialization, median witnesses and iterative correction are proved locally. The complexity result does not assert finite-precision bit complexity. Section 7 comparison lemmas establish numerical consequences of displayed inequalities, not the cited statistical lower bounds themselves.

## Build

Run from this directory:

```sh
python3 ../../scripts/verify.py --paper 34 --check static
python3 ../../scripts/verify.py --paper 34 --check build
python3 ../../scripts/verify.py --paper 34 --check comparator --suite main
python3 ../../scripts/verify.py --paper 34 --check comparator --suite negative-added-premise
python3 ../../scripts/verify.py --paper 34 --check comparator --suite negative-illegal-axiom
```

## Assumptions

Lean and Mathlib are pinned in the project files. Recovery results take `Paper34.TrigBernstein.ClassicalTrigBernstein`, the classical univariate trigonometric Bernstein inequality, as an explicit theorem argument. No proof of that interface is supplied. Chernoff and fixed-subset Hoeffding bounds are derived from Mathlib. See [external dependencies](EXTERNAL_DEPENDENCIES.md) and [exact interfaces](ExternalInputs.json).

## Verification

The complete entry and positive wrappers require a full build. Official comparison, a production audit covering private/generated declarations and fresh kernel replay have not been completed. No generated assets are required. The negative controls use the main Chebyshev recovery statement and test an added premise and an unauthorized axiom.

## References

- Queffélec–Zarouf, [On Bernstein's inequality for polynomials, Theorem 1.1](https://arxiv.org/html/1903.10801#S1.SS1).
- [Source theorem declarations](Verification/target-inventory.json).
- [Literature comparisons and their scope](ExternalComparisons.json).
