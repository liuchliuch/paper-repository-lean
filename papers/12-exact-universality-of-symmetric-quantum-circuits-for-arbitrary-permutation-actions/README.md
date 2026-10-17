# Exact universality of symmetric quantum circuits for arbitrary permutation actions

[Source paper](https://liuchliuch.github.io/repository/exact-universality-of-symmetric-quantum-circuits-for-arbitrary-permutation-actions/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1 | `Paper12.Paper.theorem_1_1` | A unitary on a finite active register has a clean symmetric circuit exactly when it is equivariant, with the stated gate and workspace bounds and the empty-register case. |
| Corollary 4.2 | `Paper12.Paper.corollary_4_2` | The construction applies to an arbitrary group action through its finite permutation image. |
| Lemma 4.1 | `Paper12.Paper.lemma_4_1` | Exact symmetric oblivious amplification of a specified block encoding whose success probability lies strictly between zero and one. |
| Appendix A | `Paper12.Paper.appendix_choi` | The Bell/swap reduction, clean amplifier, and resource bounds, conditional on the specified symmetric Choi-state preparation and register lifts. |

## Build

Use `leanprover/lean4:v4.24.0` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/verify.py --paper 12 --check static
python3 ../../scripts/verify.py --paper 12 --check build
python3 ../../scripts/verify.py --paper 12 --check comparator --suite main --local
```

## Assumptions

The source circuit model is nonuniform: exact one-qubit parameters are available, their classical computation and representation are outside the gate cost, and threshold control-set fan-in has no separate charge. The Choi appendix assumes its prescribed clean state-preparation circuit and lift symmetry. No further external mathematical theorem is assumed. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

Import `Paper12` and `Paper12.Proofs`. The actual one-hot, incidence-selection, block-encoding, and amplification constructions are included. [comparator/config.json](comparator/config.json) checks the explicit circuit and resource statements; the Choi statement retains its preparation hypotheses.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [Exact universality of symmetric quantum circuits for arbitrary permutation actions](https://liuchliuch.github.io/repository/exact-universality-of-symmetric-quantum-circuits-for-arbitrary-permutation-actions/).
