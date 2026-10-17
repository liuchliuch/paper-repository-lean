# Minimax Calibration Distance under Simultaneous Play

Lean formalization of [the source paper](https://liuchliuch.github.io/repository/deterministic-adversarial-calibration-distance/). Entry point: [`CalibrationDistance.lean`](CalibrationDistance.lean).

## Results

| Source result | Lean declaration | Mathematical scope |
| --- | --- | --- |
| Theorem 2.1 | `CalibrationDistance.source_minimax_rate` | For T ≥ 2, the two actual minimax values lie between sqrt(T)/4320 or sqrt(T)/1200 and the positive-grid infimum U_T < sqrt(T). |
| Theorem 2.1, T = 1 | `CalibrationDistance.minimax_one` | Both one-round minimax values equal 1/2. |
| Corollary 2.2 | `CalibrationDistance.horizon_free_runtime_guarantee` | One causal infinite forecaster has loss < (2+sqrt(2))sqrt(T) at every positive prefix, with exact tree/word-RAM resource guarantees. |
| Remark 2.3 | `CalibrationDistance.quantifier_order_strict_example` | A calibrated-distance example prevents exchanging expectation and supremum; the randomized-oblivious square-root lower bound remains open. |
| Lemma 4.1 | `CalibrationDistance.witness_comparison_interval` | The interval-domain Lipschitz witness comparison uses genuine least constants and supremum norm. |
| Theorems 5.1–5.2 | `CalibrationDistance.randomized_simultaneous_lower` / `CalibrationDistance.deterministic_oblivious_lower` | A deterministic past-only opponent gives the randomized lower bound; a fixed binary string gives the deterministic lower bound. |
| Lemmas 6.1–6.2 | `CalibrationDistance.shifted_bias_invariant` / `CalibrationDistance.proxy_comparison` | The grid trajectory satisfies its shifted-bias invariant and comparison with a perfectly calibrated bin-mean proxy. |
| Proposition 6.3 | `CalibrationDistance.fixed_grid_pathwise_bound` | For every binary path, the causal midpoint grid has loss at most T/(2m)+(m−1)/2. |
| Corollary 6.4 | `CalibrationDistance.optimalGrid_minimizes` | The explicit positive-integer grid optimizer minimizes the source objective; the rounding identity gives the strict square-root bound. |
| Proposition 6.5 | `CalibrationDistance.fixed_grid_exact_implementation` | Cached-tree forecasts exactly implement the grid rule, with linear initialization/space and logarithmic record visits and word width. |
| Lemma 7.1 | `CalibrationDistance.calDist_partition_le` | Calibration distance is subadditive under arbitrary finite partitions, including consecutive blocks. |

## Build

Run from this directory with Python 3.11+, Git and Lean installed through elan. The committed `lean-toolchain` and `lake-manifest.json` select the compiler and dependency revisions.

```sh
python3 ../../scripts/verify.py --paper 30 --check static
python3 ../../scripts/verify.py --paper 30 --check build
python3 ../../scripts/verify.py --paper 30 --check comparator --suite main
```

## Assumptions

No additional unformalized mathematical theorem is assumed. Behavioral strategies are Borel kernels on public histories; a simultaneous opponent sees only the strict past. A finite-horizon law reads only its initial transitions, so strategies may depend on the horizon. The implementation uses the source unit-cost word-arithmetic, record-access and continuation/root-handle model. See [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md).

## Verification

Calibration distance is the infimum over actual perfectly calibrated comparators, and U_T is independently defined over positive integer grids. Runtime statements concern exact record/word-RAM costs, arena footprints and initialization deadlines; they do not bound Lean evaluator, compiler or garbage-collector wall time. The randomized-oblivious lower-bound question is not resolved. See [verification prerequisites](../../docs/verification.md).

## References

- [Source paper: Minimax Calibration Distance under Simultaneous Play](https://liuchliuch.github.io/repository/deterministic-adversarial-calibration-distance/).
- [Mathlib formal dependencies](https://github.com/leanprover-community/mathlib4).
