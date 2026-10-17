# Lean Formalizations for the Paper Repository

Lean formalizations accompanying the 38 papers in the [Paper Repository](https://liuchliuch.github.io/repository.html). Each paper has its own project under [`papers/`](papers/), with a fixed Lean version, pinned Mathlib dependencies, documented theorem statements and explicit external assumptions.

[![Source checks](https://github.com/liuchliuch/paper-repository-lean/actions/workflows/static.yml/badge.svg)](https://github.com/liuchliuch/paper-repository-lean/actions/workflows/static.yml)

## Build

Install Python 3.11+, Git and [elan](https://github.com/leanprover/elan), then select a paper by its number:

```sh
python3 scripts/verify.py --paper 28 --check build
```

Projects that use generated certificate inputs provide a reproducible preparation command. See [building and generated inputs](docs/generated-inputs.md) for prerequisites and local generation.

## Verification

The repository uses the official [Lean Comparator](https://github.com/leanprover/comparator) with pinned tool versions and independent fixed statement specifications:

```sh
python3 scripts/setup_comparator.py --execute
python3 scripts/verify.py --paper 28 --check comparator --local
```

The second command uses the paper's primary statement configuration. `--local` explicitly selects trusted local execution without the operating-system sandbox; the statement, axiom and Lean-kernel checks remain enabled. See [verification](docs/verification.md) for toolchains, negative controls, contract preparation and the precise scope of each check.

Some results take published theorems as explicit parameters. Each paper documents these assumptions and any narrower formal scope. Computational and kernel checks are explicit commands; the repository does not imply that every expensive check has been rerun. CI checks source structure and the Python tooling.

## Papers

<!-- papers:start -->

| ID | Paper | Formalization |
|---|---|---|
| 01 | [Boundary reduction for growth-optimal e-variables: a Gaussian theorem and a finite counterexample](https://liuchliuch.github.io/repository/boundary-reduction-for-growth-optimal-e-variables-a-gaussian-theorem-and-a-finite-counterexample/) | [Lean sources](papers/01-boundary-reduction-for-growth-optimal-e-variables-a-gaussian-theorem-and-a-finite-counterexample/) |
| 02 | [A tractable streaming moment with square-root cancellation cost in symmetric Lévy decompositions](https://liuchliuch.github.io/repository/a-tractable-streaming-moment-with-square-root-cancellation-cost-in-symmetric-levy-decompositions/) | [Lean sources](papers/02-a-tractable-streaming-moment-with-square-root-cancellation-cost-in-symmetric-levy-decompositions/) |
| 03 | [Exact semidegree extraction from minimum outdegree](https://liuchliuch.github.io/repository/exact-semidegree-extraction-from-minimum-outdegree/) | [Lean sources](papers/03-exact-semidegree-extraction-from-minimum-outdegree/) |
| 04 | [Copies of K₄,₄ in K₃,₅-free graphs](https://liuchliuch.github.io/repository/copies-of-k4-4-in-k3-5-free-graphs/) | [Lean sources](papers/04-copies-of-k4-4-in-k3-5-free-graphs/) |
| 05 | [Exact Las Vegas query costs for purification with state-generating oracles](https://liuchliuch.github.io/repository/exact-las-vegas-query-costs-for-purification-with-state-generating-oracles/) | [Lean sources](papers/05-exact-las-vegas-query-costs-for-purification-with-state-generating-oracles/) |
| 06 | [The logarithmic cost of componentwise constraints in finite de Finetti approximation](https://liuchliuch.github.io/repository/the-logarithmic-cost-of-componentwise-constraints-in-finite-de-finetti-approximation/) | [Lean sources](papers/06-the-logarithmic-cost-of-componentwise-constraints-in-finite-de-finetti-approximation/) |
| 07 | [Optimal uniform sampling for stable geometric median coresets](https://liuchliuch.github.io/repository/optimal-uniform-sampling-for-stable-geometric-median-coresets/) | [Lean sources](papers/07-optimal-uniform-sampling-for-stable-geometric-median-coresets/) |
| 08 | [A deterministic FPTAS for weakly interacting continuous factor models](https://liuchliuch.github.io/repository/a-deterministic-fptas-for-weakly-interacting-continuous-factor-models/) | [Lean sources](papers/08-a-deterministic-fptas-for-weakly-interacting-continuous-factor-models/) |
| 09 | [The Griffiths exponent of random-field Ising dynamics at strong Gaussian disorder](https://liuchliuch.github.io/repository/the-griffiths-exponent-of-random-field-ising-dynamics-at-strong-gaussian-disorder/) | [Lean sources](papers/09-the-griffiths-exponent-of-random-field-ising-dynamics-at-strong-gaussian-disorder/) |
| 10 | [Strong average self-concordance of the log-determinant metric at linear scale](https://liuchliuch.github.io/repository/strong-average-self-concordance-of-the-log-determinant-metric-at-linear-scale/) | [Lean sources](papers/10-strong-average-self-concordance-of-the-log-determinant-metric-at-linear-scale/) |
| 11 | [Uniform complex border-rank bounds from all-cut Schmidt ranks](https://liuchliuch.github.io/repository/uniform-complex-border-rank-bounds-from-all-cut-schmidt-ranks/) | [Lean sources](papers/11-uniform-complex-border-rank-bounds-from-all-cut-schmidt-ranks/) |
| 12 | [Exact universality of symmetric quantum circuits for arbitrary permutation actions](https://liuchliuch.github.io/repository/exact-universality-of-symmetric-quantum-circuits-for-arbitrary-permutation-actions/) | [Lean sources](papers/12-exact-universality-of-symmetric-quantum-circuits-for-arbitrary-permutation-actions/) |
| 13 | [Exponential Lie-algebra gaps for QAOA-MaxCut on asymmetric graphs](https://liuchliuch.github.io/repository/exponential-lie-algebra-gaps-for-qaoa-maxcut-on-asymmetric-graphs/) | [Lean sources](papers/13-exponential-lie-algebra-gaps-for-qaoa-maxcut-on-asymmetric-graphs/) |
| 14 | [Strong mixing of the Boca-Cobeli-Zaharescu map](https://liuchliuch.github.io/repository/strong-mixing-bcz-map/) | [Lean sources](papers/14-strong-mixing-bcz-map/) |
| 15 | [An exact classical threshold in the binary triangle network](https://liuchliuch.github.io/repository/an-exact-classical-threshold-in-the-binary-triangle-network/) | [Lean sources](papers/15-an-exact-classical-threshold-in-the-binary-triangle-network/) |
| 16 | [Counter-Free Higher-Dimensional Automata for First-Order Interval-Pomset Languages](https://liuchliuch.github.io/repository/counter-free-higher-dimensional-automata-for-first-order-interval-pomset-languages/) | [Lean sources](papers/16-counter-free-higher-dimensional-automata-for-first-order-interval-pomset-languages/) |
| 17 | [The space of Delzant polytopes is an absolute retract](https://liuchliuch.github.io/repository/the-space-of-delzant-polytopes-is-an-absolute-retract/) | [Lean sources](papers/17-the-space-of-delzant-polytopes-is-an-absolute-retract/) |
| 18 | [Galois-modular extensions for Tannakian centers with prescribed spherical structure](https://liuchliuch.github.io/repository/galois-modular-extensions-for-tannakian-centers-with-prescribed-spherical-structure/) | [Lean sources](papers/18-galois-modular-extensions-for-tannakian-centers-with-prescribed-spherical-structure/) |
| 19 | [Highness for isomorphism at Scott rank omega_1^CK](https://liuchliuch.github.io/repository/highness-for-isomorphism-at-scott-rank-omega-1-ck/) | [Lean sources](papers/19-highness-for-isomorphism-at-scott-rank-omega-1-ck/) |
| 20 | [Counterexamples to log-concavity of local BPS invariants](https://liuchliuch.github.io/repository/counterexamples-to-log-concavity-of-local-bps-invariants/) | [Lean sources](papers/20-counterexamples-to-log-concavity-of-local-bps-invariants/) |
| 21 | [Minimax estimation of the pseudo-spectral gap at arbitrary relative precision](https://liuchliuch.github.io/repository/minimax-estimation-of-the-pseudo-spectral-gap-at-arbitrary-relative-precision/) | [Lean sources](papers/21-minimax-estimation-of-the-pseudo-spectral-gap-at-arbitrary-relative-precision/) |
| 22 | [Non-signaling reliability of classical-quantum channels with full-rank outputs](https://liuchliuch.github.io/repository/non-signaling-reliability-of-classical-quantum-channels-with-full-rank-outputs/) | [Lean sources](papers/22-non-signaling-reliability-of-classical-quantum-channels-with-full-rank-outputs/) |
| 23 | [Order-six torsion in an ordered graph configuration space](https://liuchliuch.github.io/repository/order-six-torsion-in-an-ordered-graph-configuration-space/) | [Lean sources](papers/23-order-six-torsion-in-an-ordered-graph-configuration-space/) |
| 24 | [The query complexity of uniformity testing with purified unitary access](https://liuchliuch.github.io/repository/the-query-complexity-of-uniformity-testing-with-purified-unitary-access/) | [Lean sources](papers/24-the-query-complexity-of-uniformity-testing-with-purified-unitary-access/) |
| 25 | [One-Clean-Qubit Simulation of Quantum Catalytic Logspace with Measurements](https://liuchliuch.github.io/repository/one-clean-qubit-simulation-of-quantum-catalytic-logspace-with-measurements/) | [Lean sources](papers/25-one-clean-qubit-simulation-of-quantum-catalytic-logspace-with-measurements/) |
| 26 | [Rank-dependent lower bounds for quantum chi-squared tomography](https://liuchliuch.github.io/repository/rank-dependent-lower-bounds-for-quantum-chi-squared-tomography/) | [Lean sources](papers/26-rank-dependent-lower-bounds-for-quantum-chi-squared-tomography/) |
| 27 | [At most two smooth holomorphic fibrations over hyperbolic curves](https://liuchliuch.github.io/repository/at-most-two-smooth-holomorphic-fibrations-over-hyperbolic-curves/) | [Lean sources](papers/27-at-most-two-smooth-holomorphic-fibrations-over-hyperbolic-curves/) |
| 28 | [Additivity of spherical volume under free products in dimensions at least four](https://liuchliuch.github.io/repository/additivity-of-spherical-volume-under-free-products-in-dimensions-at-least-four/) | [Lean sources](papers/28-additivity-of-spherical-volume-under-free-products-in-dimensions-at-least-four/) |
| 29 | [Near-Optimal Label Complexity for Active Huber Regression](https://liuchliuch.github.io/repository/near-linear-label-complexity-for-active-huber-regression/) | [Lean sources](papers/29-near-linear-label-complexity-for-active-huber-regression/) |
| 30 | [Minimax Calibration Distance under Simultaneous Play](https://liuchliuch.github.io/repository/deterministic-adversarial-calibration-distance/) | [Lean sources](papers/30-deterministic-adversarial-calibration-distance/) |
| 31 | [Dimension-Free Gradient-Norm Minimization in ℓₚ and Schatten-p Spaces](https://liuchliuch.github.io/repository/dimension-free-small-gradients-in-ell-p-geometry/) | [Lean sources](papers/31-dimension-free-small-gradients-in-ell-p-geometry/) |
| 32 | [Nonminimizing Limits of Noisy Clarke Subgradient Descent](https://liuchliuch.github.io/repository/counterexample-to-generic-convergence-to-local-minima/) | [Lean sources](papers/32-counterexample-to-generic-convergence-to-local-minima/) |
| 33 | [Exact Coverage Frontiers for Multi-Environment Jackknife+](https://liuchliuch.github.io/repository/exact-rank-frontier-for-multi-environment-jackknife-plus/) | [Lean sources](papers/33-exact-rank-frontier-for-multi-environment-jackknife-plus/) |
| 34 | [Scale-Independent Robust Multivariate Polynomial Regression](https://liuchliuch.github.io/repository/optimal-sample-scale-independent-robust-multivariate-polynomial-regression/) | [Lean sources](papers/34-optimal-sample-scale-independent-robust-multivariate-polynomial-regression/) |
| 35 | [Sharp Rank Laws for Maxout Switch Density](https://liuchliuch.github.io/repository/rank-linear-knot-density-for-maxout/) | [Lean sources](papers/35-rank-linear-knot-density-for-maxout/) |
| 36 | [Anytime Posterior Sampling under Nested CVaR Constraints](https://liuchliuch.github.io/repository/sparse-calibration-for-dynamic-cvar-constraints/) | [Lean sources](papers/36-sparse-calibration-for-dynamic-cvar-constraints/) |
| 37 | [Rate-Optimal Polynomial-Time Prediction of Stationary Renewal Processes](https://liuchliuch.github.io/repository/sharp-polynomial-time-renewal-prediction/) | [Lean sources](papers/37-sharp-polynomial-time-renewal-prediction/) |
| 38 | [Uniform-in-Time Particle Convergence for Projected Gaussian SVGD](https://liuchliuch.github.io/repository/uniform-in-time-particle-convergence-for-gaussian-svgd/) | [Lean sources](papers/38-uniform-in-time-particle-convergence-for-gaussian-svgd/) |

<!-- papers:end -->

## Contributing

Use the project template to add a paper without editing a central dispatch list:

```sh
python3 scripts/add_paper.py --title "Paper title" --slug paper-title --source-url https://example.org/paper
python3 scripts/catalog.py
```

See [CONTRIBUTING.md](CONTRIBUTING.md) for statement specifications, external assumptions and checks.

## License

Original code and documentation use the [MIT License](LICENSE). Third-party code retains its original notices; see [NOTICE.md](NOTICE.md). Linked research papers are not relicensed by this repository.
