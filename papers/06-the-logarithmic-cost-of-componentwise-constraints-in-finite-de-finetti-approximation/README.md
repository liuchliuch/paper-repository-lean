# The logarithmic cost of componentwise constraints in finite de Finetti approximation

[Source paper](https://liuchliuch.github.io/repository/the-logarithmic-cost-of-componentwise-constraints-in-finite-de-finetti-approximation/).

Lean formalization of constrained finite de Finetti approximation using extended KL, Borel mixing measures, and explicit matching laws. The production entry is `Paper06.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Lemma 2.1 | `Paper06.Posterior.lemma_2_1_posterior_preservation` | Actual normalized posterior preserves the linear constraints at every positive-mass observation, for any unobserved site and observed subset. |
| Proposition 2.2 | `Paper06.proposition_2_2` | Constructs a Borel probability measure on the original affine slice and proves the stated entropy/KL upper bound, including singular laws and null observations. |
| Theorem 3.1 | `Paper06.theorem_3_1_prime` | One admissible matching law chosen before k and the mixing measure satisfies both logarithmic lower bounds for 2 ≤ k, k² ≤ n, and the stated prime/parameter conditions. |
| Proposition 3.2 | `Paper06.Matching.exists_admissible_matching_law` | Normalized edge law, uniform endpoint-permutation mixture, exchangeability, and lifted fixed-input componentwise constraints. |
| Lemma 3.3 | `Paper06.lemma_3_3_full` | Unique-slope incidence count over every finite field, stochastic-channel decomposition, and the product-event/classical-maximum/beta bounds. |
| Proposition 3.4 | `Paper06.proposition_3_4` | Matching factorial moments, arbitrary Borel-mixture union bound, and binary data processing under the original beta hypothesis, including p = 1 and singular q = 0. |
| Corollary 3.5 | `Paper06.corollary_3_5` | No uniform bound of the stated sublogarithmic form exists, using actual matching laws along divergent primes. |
| Proposition 4.1 | `Paper06.proposition_4_1_dependent` | One Borel measure works for every allowed k, with input-dependent output fibers, zero input masses, and exact sampling cost including k = M. |
| Further mixture and limit statements | `Paper06.matching_noniid_logarithmic_lower_bound` | Arbitrary Borel mixtures of nonidentical feasible factors; `Matching.matchingLawFin_pair_eq` proves the two-point law and `paperOptimalError_tendsto_zero_atTop` proves the optimum tends to zero. |
| Corollary 3.6: algebra only | `Paper06.improved_polynomial_exponent` | Only exponent and constant algebra is formalized; the full improved corollary is not asserted. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 06 --check static
python3 ../../scripts/verify.py --paper 06 --check build
python3 ../../scripts/verify.py --paper 06 --check comparator --suite main
```

## Assumptions

Full Corollary 3.6 requires Bavarian–Shor’s stronger finite-field CHSH incidence theorem and is outside the proved scope. No such theorem is inserted as an axiom. The other numbered results and the mixture/limit statements use the explicit hypotheses shown in their declarations. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

KL takes values in `EReal` and is +infinity on support mismatch. The lower bounds allow arbitrary Borel mixing, including nonidentical individually feasible factors; no finite-support or full-support restriction is imposed. The main contracts exclude the full external Corollary 3.6. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/the-logarithmic-cost-of-componentwise-constraints-in-finite-de-finetti-approximation/).
- [Bavarian and Shor, Information causality, Szemerédi–Trotter and algebraic variants of CHSH, Theorem 1.3](https://arxiv.org/abs/1311.5186).
