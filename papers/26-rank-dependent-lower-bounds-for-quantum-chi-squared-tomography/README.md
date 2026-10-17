# Rank-dependent lower bounds for quantum chi-squared tomography

Lean formalization of [the source paper](https://liuchliuch.github.io/repository/rank-dependent-lower-bounds-for-quantum-chi-squared-tomography/). Entry point: [`Paper26.lean`](Paper26.lean).

## Results

| Source result | Lean declaration | Mathematical scope |
| --- | --- | --- |
| Theorem 1.2 | `Paper26.SourceCopyComplexity.theorem_1_2` | All four minimum-copy lower bounds for arbitrary measurable collective operator POVMs and raw adaptive one-copy protocols, for every d ≥ 2 and 1 ≤ r ≤ d. |
| Theorem 1.3 | `Paper26.MainUpperBounds.theorem_1_3` | Four uniform learner constructions with the source logarithmic factors, confidence guarantees, Born laws and integer consumed-copy budgets. |
| Theorem 1.3, minimum-copy form | `Paper26.MainUpperBounds.theorem_1_3_minima` | The four minimum-copy upper bounds; separate pure-state no-logarithm and dimension-one zero-copy bounds are retained. |
| Lemma 1.4, attainment | `Paper26.MeasuredChiSquaredAttainment.attainingPOVM_eq` | A finite projective measurement attains Bures chi-squared loss, including singular and infinite-loss cases, and dominates arbitrary measurable-outcome measurements. |
| Appendix A, equation (50) | `Paper26.A1MinimaxValue.equation_50` | Exact pure-state minimax risk over actual operator learners, including n = 0, d = 1 and singular outputs. |
| Equation (36) | `Paper26.PureBetaLaw.equation_36` | The exact Beta law of the actual covariant pure-state experiment. |
| Appendix B | `Paper26.ConfidenceLowerBounds.all_source_confidence_lower_bounds` | Four confidence-dependent lower bounds with the adaptive rank factor and the original source minimum-copy definitions. |
| Lemma 3.4, numerical prior | `Paper26.NumericGraphPrior.lemma_3_4_numeric` | A compact weak-H1 Gaussian-cutoff prior on the closed half-chart, with Fisher coefficient 65536. |

## Build

Run from this directory with Python 3.11+, Git and Lean installed through elan. The committed `lean-toolchain` and `lake-manifest.json` select the compiler and dependency revisions.

```sh
python3 ../../scripts/prepare.py --paper 26
python3 ../../scripts/prepare.py --paper 26 --execute
python3 ../../scripts/verify.py --paper 26 --check static
python3 ../../scripts/verify.py --paper 26 --check build
python3 ../../scripts/verify.py --paper 26 --check comparator --suite supporting
```

Preparation reconstructs fixed Comparator source from a literal independent statement template and text-edit recipes, checking exact output hashes. It does not extract statements from the current proofs.

## Assumptions

Explicit inputs cover generic Haar/Grassmann geometry and volumes, Sobolev and weak analysis, operator Radon–Nikodym representation, Frobenius learning, matrix concentration, spectral perturbation, Borel selection, binary testing, moments and Gaussian facts. Their witnesses are not constructed here. Exact hypotheses, quantifiers and Lean declarations are in [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md) and [external-inputs.json](external-inputs.json).

## Verification

The `supporting` suite compares auxiliary component statements; it is not the final theorem boundary. Final comparison requires generation followed by independent correspondence review against the source statements:

```sh
python3 scripts/prepare-contracts.py extract
python3 scripts/prepare-contracts.py materialize --review-record .lake/contract-review/approved.json
```

Run extraction after the build. The review record must contain the exact `types_sha256` and `source_tree_sha256` from the extraction, `statement_correspondence_reviewed: true`, a reviewer and substantive review notes. Materialization creates separate final contracts. Final dispatch requires the exact review-manifest SHA-256 through `--reviewed-manifest-sha256`; the gate checks the current source tree, type inventory and generated files. Extracted types alone do not establish source-statement correspondence or prove external witnesses. The [verification guide](../../docs/verification.md) describes Comparator prerequisites.

## References

- [Talenti, Best constant in Sobolev inequality](https://math.jhu.edu/~js/Math646/talenti.sobolev.pdf).
- [Harrow, The Church of the Symmetric Subspace](https://arxiv.org/pdf/1308.6595).
- [Nayak–Zhou, Optimal Low-Rank Quantum State Tomography with Bounded-Sample Joint Measurements](https://arxiv.org/html/2609.10514v1).
