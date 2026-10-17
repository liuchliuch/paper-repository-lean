# Near-Optimal Label Complexity for Active Huber Regression

Lean formalization of [the source paper](https://liuchliuch.github.io/repository/near-linear-label-complexity-for-active-huber-regression/). Entry point: [`Paper29.lean`](Paper29.lean).

## Results

| Source result | Lean declaration | Mathematical scope |
| --- | --- | --- |
| Theorem 2.1 | `Paper29.Checked.theorem21` | A label-oblivious nonadaptive query set achieves 0.99 success for each fixed response, with an absolute constant before designs, ranks and accuracies. |
| Theorem 2.2 | `Paper29.Checked.theorem22` | Adaptive distinct-query lower bound with constant 1/1280000, arbitrary measurable private seed and worst-response expected cost; unsuccessful nonreturn costs infinity. |
| Corollary 2.3 | `Paper29.Checked.corollary23` | Matching minimax bounds through actual sequentialization, preserving answers, correctness and distinct queried-set cost. |
| Lemma 3.1 | `Paper29.Checked.lemma31` | Huber triangle and increment inequalities, including their weighted forms. |
| Lemmas 3.2–3.4 | `Paper29.Checked.lemma32` / `Paper29.Checked.lemma33` / `Paper29.Checked.lemma34` | Finite normalized weight construction, endpoint coverings and all-radius label-oblivious Huber scores, under generic covering/Gram-stability inputs. |
| Lemmas 3.5–3.6 | `Paper29.Checked.lemma35` / `Paper29.Checked.lemma36` | Unshifted expectation and centered affine transfer bounds, with the displayed sampling, geometry and positive-baseline hypotheses. |
| Remark 3.7 | `Paper29.omitted_label_not_strong_affine` | The omitted-label example prevents the claimed strong affine guarantee without centering. |
| Lemmas 3.8–3.9 | `Paper29.Checked.lemma38` / `Paper29.Checked.lemma39` | All-scale extension and a label-oblivious constant-factor pilot, including the zero-optimum case in the upper-bound construction. |
| Lemmas 4.1–4.2 | `Paper29.Checked.lemma41` / `Paper29.Checked.lemma42` | Exact scalar majority gap and binary rate–distortion bound. |
| Lemma 4.3 | `Paper29.Checked.lemma43` | Information is at most per-query information times expected distinct queries, for fresh adaptive policies with an actual conditional kernel. |
| Proposition 5.1 | `Paper29.Checked.proposition51` | Explicit instances where simple surrogate minimizers have polynomially worse Huber loss. |
| Appendix A.3 | `Paper29.Checked.appendixA3` | Minimum-norm weighted Huber selection is a Borel limit of measurable unique regularized minimizers, under generic convex-selection inputs. |

## Build

Run from this directory with Python 3.11+, Git and Lean installed through elan. The committed `lean-toolchain` and `lake-manifest.json` select the compiler and dependency revisions.

```sh
python3 ../../scripts/verify.py --paper 29 --check static
python3 ../../scripts/verify.py --paper 29 --check build
python3 ../../scripts/verify.py --paper 29 --check comparator --suite main
```

## Assumptions

Explicit inputs are generic anchored chaining, Gram-radius log stability, finite-interval covering, Lewis normalization, Shannon information rules and two finite-dimensional convex-selection facts. Huber attainment, minimum-norm uniqueness and observed-label dependence are established locally. The transcript theorem assumes standard-Borel responses and an actual regular conditional kernel; it does not assert such a kernel for every arbitrary source. See [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md).

## Verification

The fixed propositions in `Specification`, `ExpandedSpecification` and `NumberedContracts` expose the precise hypotheses independently of the Checked solutions. Comparator verification of these conditional statements does not supply the external witnesses or strengthen their outcome-space assumptions. See [verification prerequisites](../../docs/verification.md).

## References

- [Jambulapati–Lee–Liu–Sidford, arXiv:2311.18145](https://arxiv.org/html/2311.18145v1).
- [Cohen–Peng, Lewis-weight sampling](https://arxiv.org/pdf/1412.0588).
- [Gray, Entropy and Information Theory](https://ee.stanford.edu/~gray/it1_corrected_6-23.pdf).
- [Bauschke–Combettes, Convex Analysis and Monotone Operator Theory](https://doi.org/10.1007/978-3-319-48311-5).
