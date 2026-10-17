# Exact Las Vegas query costs for purification with state-generating oracles

[Source paper](https://liuchliuch.github.io/repository/exact-las-vegas-query-costs-for-purification-with-state-generating-oracles/).

Lean formalization of exact purification costs using state-generating oracles, fixed query circuits, and returned catalysts. The production entry is `ELV.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1 | `ELV.theorem11_full` | For 0 < delta < 1/2 and every nonzero finite workspace, the actual unrestricted minimax value is 1/(2*delta), the admissible value is 1/(1 − sqrt(1 − 4*delta²)), and both admit separable attainments. |
| Lemma 2.1 | `ELV.Gram.stabilized_realization_full` | Equal-Gram families in complete complex Hilbert spaces admit one stabilized unitary with the exact Hilbert-basis cardinal and separability consequence. |
| Remark 2.2 | `ELV.Query.bilateralShift_no_transduction` | The concrete bilateral shift has no square-summable orthogonal returned catalyst for the stated public input/output equation. |
| Lemma 3.1 | `ELV.Line.line_purifier_public` | One fixed line circuit has the proved returned catalyst, executed query cost, and catalyst norm; `line_purifier_public_endpoint` covers both zero-catalyst endpoints. |
| Proposition 4.1 | `ELV.Costs.admissible_adversary_twoSpaces` | The admissible operational value equals the signed-Gram infimum over separately chosen complete forward/inverse spaces, with extraction and converse realization. |
| Proposition 4.2 | `ELV.Costs.oneDirection_optimum_infinite` | Forbidding either query direction forces infinite uniform cost for every admissible exact circuit and for the corresponding minimax value. |
| Four-query construction; (3.11) | `ELV.FourQuery.catalyst_bound` | The fixed four-query purifier returns its catalyst, attains the unrestricted optimum, and satisfies the catalyst bound, including endpoint oracle probabilities. |
| Introduction consequences | `ELV.Costs.costs_dimension_independent` | Dimension independence; `costs_at_quarter` gives the numeric example, and `admissible_asymptotic_remainder_bound` gives the uniform O(delta²) remainder. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 05 --check static
python3 ../../scripts/verify.py --paper 05 --check build
python3 ../../scripts/verify.py --paper 05 --check comparator --suite main
```

## Assumptions

No additional paper-specific theorem axiom is used. The declarations quantify over actual finite fixed circuits, arbitrary complete ancillary/control Hilbert spaces, and executed query norms. The cited previous-literature unrestricted upper bound 3 is background and is not reconstructed here. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The main contracts state the operational infima and separable attainments, rather than only their numerical candidate formulas. The workspace dimension is nonzero in the minimax statements; the line-circuit endpoint cases are proved separately. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/exact-las-vegas-query-costs-for-purification-with-state-generating-oracles/).
