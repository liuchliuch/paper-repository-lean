# Exact Coverage Frontiers for Multi-Environment Jackknife+

Source: [paper](https://liuchliuch.github.io/repository/exact-rank-frontier-for-multi-environment-jackknife-plus/).

## Results

The main entry is `MEJF.lean`; the default build also includes the positive theorem wrappers in `Proofs.lean`.

| Source result | Lean declaration | Scope |
| --- | --- | --- |
| Theorem 3.1 | `MEJF.MainResults.exact_failure_law` | Exact worst-case failure probability over measurable multiset learners and exchangeable complete-block laws, with attaining models. |
| Corollaries 3.2–3.6 | `MEJF.ActualPareto.ranks_eq_lattice` | Finite validity and the rank lattice; related modules prove Pareto enumeration, limiting frontiers and complete-failure regimes. |
| Theorem 6.1 | `MEJF.HeterogeneousProbability.gamma_eq` | Exact heterogeneous-size law with actual attainment. |
| Theorem 6.2 | `MEJF.Asymmetric.gamma_eq` | Exact asymmetric-rank law and its relation to symmetric ranks. |
| Theorem 6.3 | `MEJF.RandomizedProbability.gammaF_eq` | Randomized-rank minimax law with one learner/law outside the hidden-rank expectation. |
| Proposition 7.2 | `MEJF.EfficiencyCompletion.proposition_7_2` | Atomless exchangeable efficiency construction with pathwise interval-length separation. |

Randomized learners use one independent seed shared across all fits. Indexed observations and ties are retained.

## Build

Run from this directory:

```sh
python3 ../../scripts/verify.py --paper 33 --check static
python3 ../../scripts/verify.py --paper 33 --check build
python3 ../../scripts/verify.py --paper 33 --check comparator --suite main
python3 ../../scripts/verify.py --paper 33 --check comparator --suite negative-added-premise
python3 ../../scripts/verify.py --paper 33 --check comparator --suite negative-illegal-axiom
```

## Assumptions

Lean and Mathlib are pinned in the project files. Two additional interfaces remain explicit parameters: `MEJF.RankDP.LandauInput` identifies the dynamic program with the tournament optimum, and `MEJF.HeterogeneousSortingInput.PublishedMergeSortContract` supplies the optional complete sorting pipeline. Neither has a supplied Lean inhabitant. The statistical minimax identities and the algorithm after sorting do not require an assumed sorter implementation. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The aggregate entries and positive wrappers require a complete dependency-consistent build. Official comparison, a full production axiom audit and fresh kernel replay have not been completed. No asset generation is required. Negative controls test an added premise and an unauthorized axiom.

## References

- [Source-to-declaration map](Verification/coverage-map.json).
- Landau's tournament characterization: [DOI](https://doi.org/10.1007/BF02476378).
- Sedgewick–Wayne, [merge sorting](https://algs4.cs.princeton.edu/22mergesort/index.php).
