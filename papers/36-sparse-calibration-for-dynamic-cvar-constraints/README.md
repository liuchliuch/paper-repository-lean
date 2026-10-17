# Anytime Posterior Sampling under Nested CVaR Constraints

Source: [paper](https://liuchliuch.github.io/repository/sparse-calibration-for-dynamic-cvar-constraints/).

## Results

The entry module is `Paper36.lean`. The model includes randomized actions inside nested CVaR, an arbitrary original prior and a constrained comparator.

| Source result | Lean declaration | Scope |
| --- | --- | --- |
| Theorem 4.2 | `Paper36.SourceTheorems.theorem_4_2` | Signed Bayesian performance for the actual posterior-sampling process under the posterior-copy, Borel-oracle and execution specifications. |
| Theorem 4.2, calibration conclusion | `Paper36.SourceTheorems.pathwise_calibration` | One common probability-one event gives the all-K calibration count and sparse-frequency conclusions under strict feasibility. |
| Theorem 5.6 | `Paper36.SourceTheorems.risk_bank_certificate` | A fixed `(K, delta)` risk-bank certificate; it is not a confidence sequence. |
| Corollaries B.1 and B.3 | `Paper36.SourceTheorems.stage_corollary_B_1` | Certified approximate exploitation and stage-dependent tail masses; horizon-one and risk-neutral endpoints are separate statements. |
| Proposition 6.2, mathematical encoding | `Paper36.Complexity.rational_planning_encoding_exact` | Exact finite planning reductions, LP/degree-two existential-real encodings and rational payload bounds. |

The native process proves conditional physical laws, adaptation and fresh-tape/count-prefix identities. Signed debt does not imply positive-part, per-episode or realized trajectory-cost safety. General machine encoders and NP/PSPACE class transfer are external consequences, rather than Lean complexity-class predicates.

## Build

Run from this directory:

```sh
python3 ../../scripts/verify.py --paper 36 --check static
python3 ../../scripts/verify.py --paper 36 --check build
python3 ../../scripts/verify.py --paper 36 --check comparator --suite main
python3 ../../scripts/verify.py --paper 36 --check comparator --suite negative-added-premise
python3 ../../scripts/verify.py --paper 36 --check comparator --suite negative-illegal-axiom
```

## Assumptions

Lean and Mathlib are pinned in the project files. Explicit interfaces supply categorical KL/TV concentration, a uniformly costed labelled sorter and compact-section measurable maximization. Standard hardness, short rational witnesses, real-algebraic decision and binary arithmetic/class-transfer facts form a separate external boundary. Exact posterior-copy and oracle/execution identities specify the algorithm; they are not assumed performance conclusions. See [external dependencies](EXTERNAL_DEPENDENCIES.md) and [full contracts and references](EXTERNAL_INPUTS.md).

## Verification

**Compilation of `Paper36/CalibrationScan.lean` and `Paper36/ComplexityEncoding.lean` is still required; these leaf checks have no completed production artifacts.** The complete entry, fixed theorem wrappers, official comparison, full production axiom audit and fresh kernel replay also remain incomplete. No fixture generation is required. Negative controls test an added premise and an unauthorized axiom.

## References

- [Exact theorem interfaces and mathematical references](EXTERNAL_INPUTS.md).
- [Source statements and Lean declarations](Verification/targets.json).
