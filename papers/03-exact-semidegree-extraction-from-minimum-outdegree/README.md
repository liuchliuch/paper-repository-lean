# Exact semidegree extraction from minimum outdegree

[Source paper](https://liuchliuch.github.io/repository/exact-semidegree-extraction-from-minimum-outdegree/).

Lean formalization of the exact semidegree threshold, extremal digraph construction, and dense limit. The production entry is `SemidegreeExt.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Proposition 2.1 | `SemidegreeExt.prop_2_1` | Doubled integer inequality for loopless nonempty finite digraphs with feasible minimum outdegree. |
| Lemma 3.1 | `SemidegreeExt.nested_placement` | Unit-capacity pair placement with the stated row demands and column capacities, including d = 0. |
| Theorem 1.1 | `SemidegreeExt.theorem_1_1` | For 0 < n and d < n, the graph minimum equals the least integer threshold C. `qMin_eq_C`, `C_closed_form`, and `extremal_construction` provide the minimum, radical/ceiling formula, and constant-outdegree witness. |
| Corollary 1.2 | `SemidegreeExt.corollary_1_2` | For 0 < alpha < 1, the finite identity, dense limit, and original liminf equal 1 − sqrt(1 − alpha²). |
| Subdigraph consequences | `SemidegreeExt.q_le_iff_all_subdigraphs` | Vertex-and-arc-deleted subdigraphs, induced extraction equivalence, and degeneracy characterization; supporting results include monotonicity, strict comparisons, and endpoint expansions. |
| Algorithmic construction | `SemidegreeExt.ConstructionAlgorithm.fullSolve_polynomial_time` | The returned adjacency list has metered work at most 2048*n⁸. `full_construction_correct` proves looplessness, exact outdegree, optimal semidegree value, and absence of duplicate arcs. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 03 --check static
python3 ../../scripts/verify.py --paper 03 --check build
python3 ../../scripts/verify.py --paper 03 --check comparator --suite main
```

## Assumptions

No additional paper-specific theorem axiom is used. Graph hypotheses and feasibility conditions are explicit in the public declarations. See [External dependencies](EXTERNAL_DEPENDENCIES.md) for the pinned libraries and cost-model boundary.

## Verification

The algorithmic bound counts explicitly defined integer/word comparisons, list operations, and route copying. Separate theorems bound intermediate integer magnitudes and capacities. It is a mathematical operation-count result, not a compiler or wall-clock timing guarantee. The fixed contracts cover both the exact graph statement and the metered construction. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/exact-semidegree-extraction-from-minimum-outdegree/).
