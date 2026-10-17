# Nonminimizing Limits of Noisy Clarke Subgradient Descent

Source: [paper](https://liuchliuch.github.io/repository/counterexample-to-generic-convergence-to-local-minima/).

## Results

The entry module is `Paper32.lean`.

| Source result | Lean declaration | Scope |
| --- | --- | --- |
| Theorem 2.2 | `Paper32.coercive_trapping_ae` | Almost-sure trapping and convergence of Clarke-subgradient iterates under the stated conditional noise laws, support, initialization, tilt and step assumptions. |
| Corollary 2.3 | `Paper32.minimumNorm_fixed_counterexample` | A minimum Euclidean-norm measurable selection and deterministic initialization converge to a nonminimum with probability one under iid disk noise. |
| Corollary 2.5 / Target 2.1 | `Paper32.no_conull_universal_good_tilt_set` | Refutes the universal conull good-tilt claim through a proved necessary canonical iid subcase. |
| Corollary 7.1 | `Paper32.iid_uniformDisk_scaled_selected_trapping_ae` | Extends the construction to every finite positive noise radius. |
| Corollary 7.2 | `Paper32.iid_uniformEmbeddedBall_selected_trapping_ae` | Extends the construction to dimensions at least two with Euclidean-ball noise. |

The almost-sure statements concern each fixed oracle/noise pair; they do not give one common event over all policies.

## Build

Run from this directory:

```sh
python3 ../../scripts/verify.py --paper 32 --check static
python3 ../../scripts/verify.py --paper 32 --check build
python3 ../../scripts/verify.py --paper 32 --check comparator --suite main
python3 ../../scripts/verify.py --paper 32 --check comparator --suite negative-added-premise
python3 ../../scripts/verify.py --paper 32 --check comparator --suite negative-illegal-axiom
```

## Assumptions

Lean and Mathlib are pinned by `lean-toolchain`, `lakefile.toml` and `lake-manifest.json`. There are no paper-specific external theorem arguments. The DDJ framework comparison is background, not an assumed convergence theorem. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The complete entry module and fixed theorem wrappers still require a full build. Official comparison, transitive axiom checking and fresh kernel replay have not been completed. No generated data or certificate preparation is required. The negative controls are expected to fail for a changed theorem type and an unauthorized axiom, respectively.

## References

- [Source-to-declaration map](Verification/original-result-map.json).
- [Dependency details](EXTERNAL_DEPENDENCIES.md).
