# A tractable streaming moment with square-root cancellation cost in symmetric Lévy decompositions

[Source paper](https://liuchliuch.github.io/repository/a-tractable-streaming-moment-with-square-root-cancellation-cost-in-symmetric-levy-decompositions/).

Lean formalization of the separation between tractable streaming moments and symmetric Lévy cancellation cost. The production entry is `Paper02.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1 | `Paper02.Main.theorem_1_1` | Actual bit-space streaming membership, cancellation bounds in ENNReal, square-root asymptotics, and failure of the original bivariate polynomial implication. |
| Lemma 2.1; Corollary 2.2; Remark 2.3 | `Paper02.LSym.positive_second_difference_measure` | Positive circle measure for the original Lévy cone; `dual_general_norm` and the normalized-generator results give the dual inequality and representation consequences. |
| Lemmas 2.4–2.5 | `Paper02.RS.exact_pairing` | Rudin–Shapiro energy/norm and transition identities, including the exact parity-dependent pairing and endpoint correction. |
| Proposition 3.1; Corollary 3.2 | `Paper02.LowerBound.prop_3_1` | Cancellation lower bound for the original cone and the strict all-cutoff consequence. |
| Proposition 3.3 | `Paper02.Fourier.prop_3_3` | Exact finite real-even Fourier–Hahn split and square-root cancellation envelope. |
| Proposition 3.4; Lemma A.2 | `Paper02.StreamingTractability.proposition_3_4` | Halting one-pass program for arbitrary integer updates with a final-vector bound; `GenericTractability.lemma_A2` treats bounded weights with the stated evaluator hypothesis. |
| Lemma A.1: correctness and space | `Paper02.SparseRecoverySpace.summary_and_decoder_quadratic` | Sparse/dense recovery, checksum probability, and actual decoder workspace. Polynomial Gaussian-elimination runtime is not formalized. |
| Lemma B.1 | `Paper02.Bernstein.lemma_B1` | Analytic complete-Bernstein/Pick kernel properties over the stated parameter range. |
| Propositions B.2–B.3: estimates | `Paper02.Bernstein.prop_B2_admissibleSplit` | Approximation, finite-difference, envelope, and cost estimates, together with `prop_B3_admissibleSplit` and `prop_B3_cost_bound`. The general positive-representation membership bridge is not proved. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 02 --check static
python3 ../../scripts/verify.py --paper 02 --check build
python3 ../../scripts/verify.py --paper 02 --check comparator --suite main
```

## Assumptions

The main separation and streaming theorem uses no paper-specific external axiom. The full membership conclusions of B.2–B.3 require the analytic-to-positive-measure Bernstein representation theorem. The ancillary polynomial-time claim in A.1 requires a costed finite-field Gaussian-elimination result. These consequences are outside the proved scope; correctness, probability, space, and the paper-specific analytic estimates remain proved. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The executable model charges randomness, online summaries, input buffers, update microcode, decoding, weight evaluation, and output/median computation. The main contracts include the complete streaming and separation statement. The external Bernstein representation and Gaussian-elimination runtime consequences are not certified by these contracts. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/a-tractable-streaming-moment-with-square-root-cancellation-cost-in-symmetric-levy-decompositions/).
- [Schilling, Song and Vondraček, Bernstein Functions, second edition, Chapters 3 and 6](https://doi.org/10.1515/9783110269338).
- [Håstad, Advanced Algorithms notes, §2.1.2, Theorem 2.4](https://www.csc.kth.se/~johanh/algnotes.pdf).
