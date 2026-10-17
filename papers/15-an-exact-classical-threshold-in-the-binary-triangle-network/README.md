# An exact classical threshold in the binary triangle network

[Source paper](https://liuchliuch.github.io/repository/an-exact-classical-threshold-in-the-binary-triangle-network/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1 | `Paper15.theorem1_sharp_bound` | Every measurable independent-source `TriangleModel` with stochastic binary responses and M1 = M3 = 0 satisfies M2 ≤ tStar. `theorem1_attained` gives exact attainment. |
| Corollary 2 | `Paper15.corollary2_iff` | For 0 ≤ t ≤ 1, the actual eight-outcome distribution p_t is triangle local exactly when t ≤ tStar. |
| Lemma 3 | `Paper15.lemma3_bounded_measurable` | A bounded measurable finite-dimensional map has a barycentre represented by at most d + 1 samples from any prescribed full-measure set. |
| Lemma 4 | `Paper15.lemma4_general_reduction` | One deterministic ternary maximum dominates all measurable stochastic triangle models. |
| Lemma 5 | `Paper15.lemma5_certified_gap` | Every nonexceptional ternary response table satisfies the 9/25 gap for all simplex laws, including boundary laws. |
| Lemma 6 | `Paper15.lemma6_derivative_independent` | The actual moment gradients are linearly independent under the stated positive-coordinate hypotheses. |
| Lemma 7 | `Paper15.lemma7_stationary` | Interior constrained stationarity forces the three source-coordinate pairs to coincide. |

## Build

Use `leanprover/lean4:v4.24.0` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/prepare.py --paper 15
python3 ../../scripts/prepare.py --paper 15 --execute
python3 ../../scripts/prepare.py --paper 15 --check
python3 ../../scripts/verify.py --paper 15 --check static
python3 ../../scripts/verify.py --paper 15 --check build
python3 ../../scripts/verify.py --paper 15 --check comparator --suite main --local
```

Preparation is explicit and can be expensive. The first command displays a plan; `--execute` generates locally, and `--check` checks output hashes. A build never starts generation automatically.

## Assumptions

The threshold `tStar` is the unique root in (9/25, 37/100) of 3t⁴ + 28t³ + 66t² − 36t + 3. The universal theorem permits arbitrary measurable independent source spaces and stochastic binary kernels. The finite-gap inputs are generated data checked by Lean, rather than assumed mathematical results. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The finite-gap proof requires the locally generated binaries and chunk modules listed in [generated-artifacts.json](generated-artifacts.json). Preparation uses Python 3, a native C++17 compiler with `__int128_t`, and Boost.Multiprecision headers. `CXX` selects the compiler; optional `BOOST_INCLUDEDIR` supplies the headers. Both host and compiler target must be little endian. The neighbour generator needs a 512 MiB lookup table before other memory.

Preparation installs only outputs matching every frozen hash. The Lean elaborators reconstruct ordinary terms and kernel-checked declarations from these untrusted inputs. Import `Paper15`; the exact statements are checked by [Verification/comparator.json](Verification/comparator.json). Generation, a production build, and a full Comparator replay are separate computations.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [An exact classical threshold in the binary triangle network](https://liuchliuch.github.io/repository/an-exact-classical-threshold-in-the-binary-triangle-network/).
