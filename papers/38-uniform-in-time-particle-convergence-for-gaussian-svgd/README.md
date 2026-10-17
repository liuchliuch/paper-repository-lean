# Uniform-in-Time Particle Convergence for Projected Gaussian SVGD

Source: [paper](https://liuchliuch.github.io/repository/uniform-in-time-particle-convergence-for-gaussian-svgd/).

## Results

The entry module is `Paper38.lean`. Transport costs are defined through actual quadratic Kantorovich couplings.

| Source result | Lean declaration | Scope |
| --- | --- | --- |
| Theorem 2.1 | `Paper38.Main.theorem21` | Deterministic projected Gaussian flow and uniform-in-time particle comparison under the analytic baseline family. |
| Theorem 2.2 / Corollary 2.5 | `Paper38.Main.theorem22`, `Paper38.Main.corollary25` | Expected source rates with analytic and positive-dimensional statistical baselines. |
| Proposition 2.3 | `Paper38.Main.proposition23` | Sharp raw empirical lower rate using the positive-dimensional matching input. |
| Theorem 2.4 | `Paper38.Main.theorem24` | High-probability trajectory and standardized-shape bounds under the explicit baseline families. |
| Proposition 2.6 | `Paper38.Main.proposition26` | Finite particle limit under the analytic baselines. |
| Corollary 2.7 | `Paper38.Main.corollary27` | Arbitrary-law non-Gaussian initialization and its spectral obstruction, using raw iid strong laws and transport separation. |

Constants are chosen before varying sample sizes, tail parameters, trajectories and times. Corollary 2.7 uses finite second moments without a fourth-moment assumption.

## Build

Run the static check from this directory:

```sh
python3 ../../scripts/verify.py --paper 38 --check static
```

Prepare the source-facing comparison contracts:

```sh
python3 scripts/prepare-source-certificates.py prepare
```

This checks frozen source hashes and materializes explicit signatures without running Lean. Independently compare every generated signature with the source specification, including analytic/statistical and arbitrary-law parameters. After that review, use the exact printed manifest SHA256:

```sh
python3 scripts/prepare-source-certificates.py check-reviewed REVIEWED_SHA256
python3 ../../scripts/verify.py --paper 38 --check build
python3 ../../scripts/verify.py --paper 38 --check comparator --suite main --reviewed-manifest-sha256 REVIEWED_SHA256
python3 ../../scripts/verify.py --paper 38 --check comparator --suite negative-added-premise --reviewed-manifest-sha256 REVIEWED_SHA256
python3 ../../scripts/verify.py --paper 38 --check comparator --suite negative-illegal-axiom --reviewed-manifest-sha256 REVIEWED_SHA256
```

The verifier checks the reviewed source/fixture hashes before comparison. Hash equality does not perform semantic review. Preparation refuses to overwrite generated fixtures; inspect changed inputs and repeat the review before regeneration.

## Assumptions

Lean and Mathlib are pinned in the project files. Named external interfaces supply raw Gaussian matching, covariance/concentration and initialized moments; standard ODE, Gaussian integration-by-parts and matrix-root analysis; and arbitrary-law empirical strong laws/transport separation. These are theorem arguments without supplied inhabitants. See [external dependencies](EXTERNAL_DEPENDENCIES.md) and [exact interfaces](EXTERNAL_INPUTS.md).

`Main.AnalyticBaselines` ranges over all dimensions. `Main.StatisticalBaselines` ranges only over `d ≥ 1`; no positive matching lower bound is requested at dimension zero. Corollary 2.7 adds raw strong laws over arbitrary measurable spaces and zero-cost transport separation, without Gaussian statistical baselines. `LogWishart` is an unused alternative, and `ExternalWishartEndpoint.EndpointFacts` is explanatory context rather than a rate assumption.

## Verification

Source-facing contracts have not been materialized or reviewed. Their build and official comparison, the complete production build, full axiom audit and fresh kernel replay remain incomplete. The existing `components` suite checks supporting identities only. Full negative controls test an added premise and an unauthorized axiom. Mobility, energy geometry, stability, whitening and particle-limit conclusions remain separate from the generic external interfaces.

## References

- [Analytic/statistical theorem statements, references and use sites](EXTERNAL_INPUTS.md).
- Source specifications: `Paper38/Specification.lean`, `GeometrySpecification.lean`, `SourceAffine.lean` and `SourceSamplingLemmas.lean`.
