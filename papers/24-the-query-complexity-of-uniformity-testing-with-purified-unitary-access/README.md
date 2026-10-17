# The query complexity of uniformity testing with purified unitary access

[Source paper](https://liuchliuch.github.io/repository/the-query-complexity-of-uniformity-testing-with-purified-unitary-access/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1, promise-only adaptive queries | `PUT.Paper.theorem1_promised` | For d ≥ 2 and 0 < ε < 1/2, every tester with success ≥ .99 has Q ≥ c·min(d^(1/3)/ε^(4/3), √d/ε), with a positive universal c and a query budget required only on promised inputs. |
| Theorem 1, adaptive/fixed circuits | `PUT.Paper.theorem1_adaptive` | Adaptive measurements, query directions and early stopping are included; `PUT.Paper.theorem1` is the fixed-unitary version. |
| Lemma 1 | `PUT.FullQueryBound.query_norm_le_printed` | The actual Fourier–Dirichlet adversary and complete reflection queries satisfy the printed operator-norm bound, including whole radial complements. |
| Lemma 2 | `PUT.lemma2_from_joint_moments` | The continuous Dirichlet event has probability at least 1/144 for d ≥ 2 and a ≥ 1. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/verify.py --paper 24 --check static
python3 ../../scripts/verify.py --paper 24 --check build
python3 ../../scripts/verify.py --paper 24 --check comparator --suite main
```

## Assumptions

Four explicit published inputs remain: the normalized-Gamma Dirichlet joint-moment law, ninefold coherent amplification, Kutin’s four-to-one collision lower bound, and adaptive unitary normalization. The fixed-unitary theorem uses the first three. Their exact statements and specializations are in [External dependencies](EXTERNAL_DEPENDENCIES.md). The hard priors, full operator estimates, query progress, exact collision simulation and finite-register realization are internal deductions.

## Verification

The matching upper bound and its tightness consequence, and amplification from arbitrary fixed success greater than 1/2, are not formalized. The specific .99 lower bound retains the disclosed standard inputs. `PUT.theorem1` is a numerical positivity helper; the operational lower bounds are `PUT.Paper.theorem1` and its adaptive/promise-only variants.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/PUT-the_query_complexity_of_uniformity_testing_with_purified_unitary_access.pdf).
- [NIST DLMF 5.14.2, the multivariate beta integral](https://dlmf.nist.gov/5.14.E2).
- [Watrous, Quantum Computational Complexity](https://cs.uwaterloo.ca/~watrous/Papers/QuantumComputationalComplexity.pdf).
- [Kutin, Quantum lower bound for the collision problem with small range](https://theoryofcomputing.org/articles/v001a002/v001a002.pdf).
