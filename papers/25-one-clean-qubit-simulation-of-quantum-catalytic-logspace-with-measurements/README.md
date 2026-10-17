# One-Clean-Qubit Simulation of Quantum Catalytic Logspace with Measurements

Lean formalization of [the source paper](https://liuchliuch.github.io/repository/one-clean-qubit-simulation-of-quantum-catalytic-logspace-with-measurements/). Entry point: [`Paper25.lean`](Paper25.lean).

## Results

| Source result | Lean declaration | Mathematical scope |
| --- | --- | --- |
| Theorem 1 | `Paper25.CompleteSimulation.theorem1` | Polynomial-size deterministic-logspace-uniform simulation by the constructed one-clean-qubit circuit family, with a common inverse-polynomial signed Born bias. |
| Exact-class corollary | `Paper25.CompleteSimulation.theorem1_exact` | The same circuit construction for exact source acceptance; the stated effective-gate convention is retained. |
| Lemma 2 | `Paper25.lemma_2_semantic_restoration` | Complete positivity and restoration of every catalyst density operator imply one product output state for every operator, with reference-system preservation. |
| Lemma 3 | `Paper25.KrausChannel.liouville_frob_bound_card` | The squared Frobenius norm of the actual Kraus-channel Liouville matrix is at most the square of its dimension. |
| Lemma 4 | `Paper25.lemma_4` | For invertible finite complex matrices and positive lambda, nuclear-norm regularization error is at most lambda/2 times the inverse squared Frobenius norm. |
| Lemma 5 | `Paper25.coherentWalkFilter_error` | The concrete coherent filter has the stated compression error, given a unitary eigenbasis and the explicit precision bound. |
| Lemma 6 | `Paper25.OneCleanQubit.ancillary_block_readout` | One-clean-probe density evolution gives the trace/Born readout identity used by the simulator. |

## Build

Run from this directory with Python 3.11+, Git and Lean installed through elan. The committed `lean-toolchain` and `lake-manifest.json` select the compiler and dependency revisions.

```sh
python3 ../../scripts/verify.py --paper 25 --check static
python3 ../../scripts/verify.py --paper 25 --check build
python3 ../../scripts/verify.py --paper 25 --check comparator --suite full
```

## Assumptions

The simulation retains generic classical logspace-description closure, elementary real-function approximation, a finite complex unitary spectral theorem, and the fixed ideal QFT network identity. The effective elementary-gate convention and primitive description machines are model assumptions. Their exact interfaces and source hypotheses are in [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md).

## Verification

The `full` comparison checks explicit operational statements, including the complete uniform native simulation. The `supporting` comparison covers auxiliary results. Challenge placeholders and deliberate premise/axiom controls are separate from the production imports. Conditional theorem checking does not construct the external inputs. See the [verification guide](../../docs/verification.md) for the pinned Comparator and sandbox prerequisites.

## References

- [Axler, Linear Algebra Done Right, Theorem 7.55](https://linear.axler.net/LADR4e.pdf).
- [Jones, Computability and Complexity, Section 21.6](https://hjemmesider.diku.dk/~neil/comp2book2007/book-whole.pdf).
- [Jeřábek, Elementary analytic functions in VTC⁰](https://arxiv.org/pdf/2206.12164v3).
- [Cleve–Ekert–Macchiavello–Mosca, Quantum Algorithms Revisited](https://arxiv.org/pdf/quant-ph/9708016).
