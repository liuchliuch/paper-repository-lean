# Optimal uniform sampling for stable geometric median coresets

[Source paper](https://liuchliuch.github.io/repository/optimal-uniform-sampling-for-stable-geometric-median-coresets/).

Lean formalization of optimal uniform-without-replacement sampling for stable geometric median coresets in Euclidean and finite-dimensional l1 spaces. The production entry is `GeometricMedianCoresets.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.2 | `GeometricMedianCoresets.Euclidean.sample_complexity_theta` | The least uniform sample threshold is Theta(epsilon⁻²) as epsilon tends to zero from above. For 0 < epsilon < 1/4, `thm_1_2_i` proves 4/5 success above ceil(20/epsilon²). For 0 < epsilon ≤ 1/100, `thm_1_2_ii` gives distinct one-dimensional populations with 2/5 failure below 1/(24200*epsilon²). |
| Lemma 2.1 | `GeometricMedianCoresets.Euclidean.feature_dist_sq` | Actual Gaussian-product/Lebesgue L2 embedding with the exact normalization, indicator formula, anchoring, and squared-distance identity. |
| Lemmas 2.2–2.3 | `GeometricMedianCoresets.FinitePopulation.variance_identity` | Cost-difference identity and full uniform finite-population variance for n > 1 and 1 ≤ m ≤ n; the anchored bound also includes n = 1. |
| Proposition 2.4; Lemma 2.6 | `GeometricMedianCoresets.Euclidean.prop24` | Simultaneous relative comparison for every candidate pair inside a 9/10-probability event, followed by deterministic stability transfer, including zero OPT. |
| Remark 2.5 | `GeometricMedianCoresets.Remark25.outlier_obstruction` | Explicit repeated-zero/outlier population with exact missing probability, optimum, and comparison error. |
| Corollary 4.1 | `GeometricMedianCoresets.NegativeTypeMetric.cor41_uniform_stable` | Uniform-sampling 4/5 guarantee for the paper’s negative-type metric definition, with its attained-median hypothesis. |
| Corollary 4.2 | `GeometricMedianCoresets.L1.sample_complexity_theta` | Actual finite-dimensional l1 feature map and attained median, matching sample constants, and least-threshold Theta rate. |
| Proposition 4.3 | `GeometricMedianCoresets.prop43_uniform_stable` | Approximate-reference guarantee under the stated relative-cost and scalar conditions; `uniform_stable_without_attainment` gives the delta < 1/37 consequence. |
| Proposition A.1 | `GeometricMedianCoresets.Euclidean.propA1_comparison` | Both conclusions, with the source constants involving 320*pi, follow from the stronger proved relative comparison. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 07 --check static
python3 ../../scripts/verify.py --paper 07 --check build
python3 ../../scripts/verify.py --paper 07 --check comparator --suite main
```

## Assumptions

No additional paper-specific theorem axiom is used. The Gaussian embedding and finite-dimensional median existence are proved. The general negative-type result retains its attained-median premise; approximate-reference results have their own explicit scalar conditions. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

Sampling is the actual uniform law on m-subsets. The lower construction may choose a larger population while preserving the stated sample constant and failure probability. Proposition A.1 is proved from a stronger theorem; its alternative projected-martingale derivation is not duplicated. The `main` contracts cover the probability and threshold statements; the `supporting` contracts concern only deterministic components. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/optimal-uniform-sampling-for-stable-geometric-median-coresets/).
