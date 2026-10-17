# Counter-Free Higher-Dimensional Automata for First-Order Interval-Pomset Languages

[Source paper](https://liuchliuch.github.io/repository/counter-free-higher-dimensional-automata-for-first-order-interval-pomset-languages/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1 | `CounterFreeHDA.Cubical.theorem_1_1_fromFunctor` | A finite aperiodic recognizing functor yields a finite counter-free HDA with exactly the recognized language. |
| Effective realization | `CounterFreeHDA.Cubical.FinitePomsetRecognizer.effective_realization` | A finite-table construction with bijective cell-array decoding and explicit face restrictions. |
| Interface refinement, §4 | `CounterFreeHDA.Cubical.FinitePomsetRecognizer.interface_uniform_bound` | The same HDA stabilizes at every n ≥ 2r + h for interface size r, including n ≥ h when r = 0, without an internal-width ≤ r premise. |
| Corollary 1.2: new direction | `CounterFreeHDA.Cubical.corollary_1_2_new_direction` | The new realization implication from the stated aperiodic recognizability hypothesis. |
| Appendix | `CounterFreeHDA.Appendix.Compare.actual_language_equality` | The original eight-cell HDA and its completion recognize the same language; the library also gives residual and deletion-profile calculations. |

## Build

Use `leanprover/lean4:v4.24.0` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/verify.py --paper 16 --check static
python3 ../../scripts/verify.py --paper 16 --check build
python3 ../../scripts/verify.py --paper 16 --check comparator --suite main --local
```

## Assumptions

The realization theorem retains the finite aperiodic recognizing-functor, downward-closure, and bounded-width hypotheses. The other characterization directions in Corollary 1.2 and the Appendix A.1 inference of aperiodic recognizability use external results of Erlich, Ledent, and Ziemiański and are not proved here. The realization construction and the concrete Appendix language and profile calculations are proved internally. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

Import `CounterFreeHDA`. [Verification/comparator.json](Verification/comparator.json) checks the explicit realization, effective-construction, endpoint-stability, and Appendix statements. The interface refinement concerns the same constructed HDA and includes the empty-interface case.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [Counter-Free Higher-Dimensional Automata for First-Order Interval-Pomset Languages](https://liuchliuch.github.io/repository/counter-free-higher-dimensional-automata-for-first-order-interval-pomset-languages/).
- E. Erlich, J. Ledent, and K. Ziemiański, *Algebraic characterization of FO-definable languages of higher-dimensional automata*, CONCUR 2026, Theorem 33 and Proposition 35. [DOI](https://doi.org/10.4230/LIPIcs.CONCUR.2026.32).
