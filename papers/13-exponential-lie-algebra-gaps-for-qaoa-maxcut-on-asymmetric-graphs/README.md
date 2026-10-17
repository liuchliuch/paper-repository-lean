# Exponential Lie-algebra gaps for QAOA-MaxCut on asymmetric graphs

[Source paper](https://liuchliuch.github.io/repository/exponential-lie-algebra-gaps-for-qaoa-maxcut-on-asymmetric-graphs/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1 | `Paper13.theorem1_actual` | For k ≥ 7, the constructed connected rigid graph has 7k vertices, 9k − 1 edges, maximum degree five, and the stated exponential lower bound for the natural/standard Lie-algebra dimension ratio. |
| Corollary 2 | `Paper13.corollary2_actual` | Positive-parity irreducible-component and additive-deficit bounds; `corollary2_actual_limit` proves the normalized deficit tends to one. |
| Lemma 3 | `Paper13.lemma3`, `Paper13.localP_tensor_factor` | The invariant port projector, its rank, tensor factorization, and required operator commutation properties. |
| Lemma 4 | `Paper13.lemma4` | The constructed graph is connected, asymmetric, nonbipartite, and noncyclic, with the exact size and degree bounds. |
| Proposition 5 | `Paper13.proposition5_actual` | Ported-projector hypotheses imply the assembly bounds; the divergence theorem also assumes the stated eventual graph properties. |
| Appendix A correction | `Paper13.corrected_certificate_identity` | The corrected identity 64P = I + printedCertificate + piSwap(1,6)·piSwap(3,5). `printedCertificate_not_commute` proves the printed certificate does not commute. |

## Build

Use `leanprover/lean4:v4.24.0` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/verify.py --paper 13 --check static
python3 ../../scripts/verify.py --paper 13 --check build
python3 ../../scripts/verify.py --paper 13 --check comparator --suite main --local
```

## Assumptions

The main graph family has its graph properties proved internally. The general amplification theorem retains the explicit `PortedGadget` projector hypotheses. The operator-space and dimension classification used by the bounds is reconstructed in Lean. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

Import `Paper13`. [comparator/config.json](comparator/config.json) checks the explicit operator, graph, dimension, and asymptotic statements. Appendix A is a correction with a nonzero commutator witness; the false printed commutation claim is not asserted.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [Exponential Lie-algebra gaps for QAOA-MaxCut on asymmetric graphs](https://liuchliuch.github.io/repository/exponential-lie-algebra-gaps-for-qaoa-maxcut-on-asymmetric-graphs/).
