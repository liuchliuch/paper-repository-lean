# Strong average self-concordance of the log-determinant metric at linear scale

[Source paper](https://liuchliuch.github.io/repository/strong-average-self-concordance-of-the-log-determinant-metric-at-linear-scale/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.3: probability estimate | `Paper10.Main.thm_1_3_two_sided` | The actual Gaussian proposal satisfies the two-sided local-norm estimate at radius ε^(3/2)/√864, for q > 0 and s ≥ (q + 1)/2. |
| Theorem 1.3: uniform SASC | `Paper10.Main.thm_1_3_uniform` | A single radius works for all allowed orders, scales, positive-definite base points, and positive-semidefinite auxiliary precisions. |
| Theorem 1.3: SSC threshold | `Paper10.Main.thm_1_3_ssc` | For positive order and scale, strong self-concordance holds exactly when s ≥ (q + 1)/2. |
| Theorem 1.3: minimum scale | `Paper10.Main.thm_1_3_min_scale` | The least positive scale satisfying both SSC and SASC is (q + 1)/2. |

## Build

Use `leanprover/lean4:v4.24.0` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/verify.py --paper 10 --check static
python3 ../../scripts/verify.py --paper 10 --check build
python3 ../../scripts/verify.py --paper 10 --check comparator --suite main --local
```

## Assumptions

The declarations retain the stated dimension, positivity, and matrix hypotheses. Gaussian moment bounds and the derivative identities are proved in the library and discharged by the main theorems. No additional external mathematical theorem is assumed. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

Import `Paper10` for the production library. The checks in [Verification/comparator.json](Verification/comparator.json) cover the main probability estimates, exact thresholds, Gaussian laws, and supporting calculus. Auxiliary concentration lemmas have moment hypotheses; the main theorem proves those inputs.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [Strong average self-concordance of the log-determinant metric at linear scale](https://liuchliuch.github.io/repository/strong-average-self-concordance-of-the-log-determinant-metric-at-linear-scale/).
