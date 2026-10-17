# Strong mixing of the Boca-Cobeli-Zaharescu map

[Source paper](https://liuchliuch.github.io/repository/strong-mixing-bcz-map/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1 | `Paper14.Theorem1` | Strong mixing of the BCZ map; `Theorem1L2`, `Theorem1ComplexL2`, and `finite_block_mixing` give correlation and observation-block forms. |
| Lemma 2 | `Paper14.Lemma2` | Self-induction, first-return conjugacy, measure transfer, and accumulated roof-time scaling. |
| Proposition 3 | `Paper14.Proposition3` | Product ergodicity and weak mixing of the actual BCZ system. |
| Theorem 4 | `Paper14.Theorem4` | The general mixing criterion under the original excess-return hypotheses and quantifier order. |
| Lemma 5 | `Paper14.Lemma5` | The primitive-point void-probability estimate, including finite-prime sieve moments and residual probability bounds. |

## Build

Use `leanprover/lean4:v4.24.0` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/verify.py --paper 14 --check static
python3 ../../scripts/verify.py --paper 14 --check build
python3 ../../scripts/verify.py --paper 14 --check comparator --suite main --local
```

## Assumptions

The BCZ conclusions include the section and horocycle ergodicity arguments. The general excess-return criterion retains its own stated hypotheses. No additional external theorem is assumed. Adapted proved background sources and their licenses are described in [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

Import `Paper14`. The ambient-plane measure is zero outside the Farey triangle, with the source null-set conventions for return maps. Mixing is along all natural iterates tending to infinity; no rate is claimed. [Verification/comparator.json](Verification/comparator.json) checks the explicit numbered results and correlation statements.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [Strong mixing of the Boca-Cobeli-Zaharescu map](https://liuchliuch.github.io/repository/strong-mixing-bcz-map/).
- [Vendored background sources and upstream revisions](Paper14/Background/UPSTREAM.json); [Apache-2.0 license](Paper14/Background/LICENSE).
