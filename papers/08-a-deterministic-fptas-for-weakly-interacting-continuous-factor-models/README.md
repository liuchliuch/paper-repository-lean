# A deterministic FPTAS for weakly interacting continuous factor models

[Source paper](https://liuchliuch.github.io/repository/a-deterministic-fptas-for-weakly-interacting-continuous-factor-models/).

Lean formalization of deterministic approximation for continuous factor models, including zero-free analysis, rational algorithms, and bit/query complexity. The production entry is `Paper08.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Assumption 1.1 | `Paper08.EffectiveAccess.Oracle` | Explicit effective value-access promise: cube points, positive precision, binary rational replies, polynomial time, and answer-length bounds. |
| Theorem 1.2 | `Paper08.OriginalTheorems.theorem_1_2` | From fixed arity, occurrence, range, Lipschitz, weak-interaction, and effective-access promises: actual rational partition-integral approximation, e±epsilon error, polynomial bit/query/oracle costs, and logarithmic precision. The exponent is chosen before oracle degrees and model inputs. |
| Corollary 1.3 | `Paper08.OriginalTheorems.corollary_1_3_ge_two` | Original primal-degree model for eta ≥ 2, preserving the factor family, integral, and oracle handles; `LowDegreeGuarantee.corollary_1_3_eta_one_full_guarantee` covers eta = 1. |
| Lemma 2.1 | `Paper08.CubeZeroFreeMain.original_closed_disk` | Common closed zero-free disk for every factor subcollection, proved from the original model promises. |
| Lemma 2.2 | `Paper08.OriginalTheorems.lemma_2_2` | Normalized analytic logarithm, coefficient bounds, Taylor remainder, and half-disk bounds. |
| Lemma 2.3 | `Paper08.ModelSupport.connected_support_identity` | Actual product-integral factorization, formal logarithm, Möbius support extraction, and disconnected-support cancellation. |
| Lemma 3.1 | `Paper08.Quadrature.dyadic_quadrature_error` | Total-level quadrature for overlapping scopes; `QuadratureRealOperationCount.countedRule_operations` counts the arbitrary-real sampled-function evaluator. |
| Lemma 3.2 | `Paper08.Quadrature.dyadic_stored_sample_perturbation` | The stated perturbation bounds for finite total-level rules and reused stored samples. |
| Lemma 3.3 | `Paper08.PrimitiveAlgorithm.lemma33` | Rational primitive moments, multinomial assembly, error, precision, denominator/height, binary execution, and oracle-time bounds. |
| Lemma 4.1 | `Paper08.OriginalTheorems.lemma_4_1` | Stability of the actual local moment/logarithmic recurrence under the source perturbation conditions. |
| Lemma A.1 | `Paper08.LowDegreeGuarantee.lemma_A1_full_guarantee` | Actual component-grid algorithm for primal degree at most one, including n = 0 and complete graph/grid/control costs. |
| Proposition B.1 | `Paper08.LowerBound.prop_B1_finite_precision` | Adaptive deterministic finite-precision query lower bound; `prop_B1_sampling_omega` gives the explicit sampling scale and `GridSurrogate.prop_B1_converse` proves the surrogate upper scale. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 08 --check static
python3 ../../scripts/verify.py --paper 08 --check build
python3 ../../scripts/verify.py --paper 08 --check comparator --suite main
```

## Assumptions

Assumption 1.1 is an explicit oracle-access promise, not an existence theorem for arbitrary real functions. No additional paper-specific theorem axiom is used. Common finite-cube nonvanishing is proved internally, so the public original main theorem and corollary have no extra `CommonNonvanishing` hypothesis. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The complexity model charges ordinary binary multiplication, long division, rational normalization, floor/ceiling, enumeration, sorting, graph/grid/coordinate controls, and oracle time. It is not a verified-compiler or Lean VM wall-clock claim. The `main` contracts include the original model hypotheses and implemented algorithm; the `supporting` contracts cover auxiliary estimates only. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/a-deterministic-fptas-for-weakly-interacting-continuous-factor-models/).
