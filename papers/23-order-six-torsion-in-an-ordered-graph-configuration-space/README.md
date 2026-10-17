# Order-six torsion in an ordered graph configuration space

[Source paper](https://liuchliuch.github.io/repository/order-six-torsion-in-an-ordered-graph-configuration-space/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1, cubical homology | `Paper23.discrete_result` | An explicit class of order 6, with multiples of orders 3 and 2, in the actual ordered-cube cycles/boundaries quotient; no certificate premise is added. |
| Theorem 1, source space | `Paper23.main_result` | The corresponding class in integral singular H₂ of four ordered particles on the six-vertex, thirteen-edge core multigraph, relative to the two topology inputs. |
| Simple presentation | `Paper23.simple_presentation_result` | The same result for the homeomorphic eight-vertex, fifteen-edge simple graph presentation. |
| Graph hypotheses | `Paper23.GraphGirth.fourParticleConditions` | Connectedness, special-vertex path lengths and girth conditions for the explicit subdivision. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/prepare.py --paper 23 --execute
python3 ../../scripts/verify.py --paper 23 --check static
python3 ../../scripts/verify.py --paper 23 --check build
python3 ../../scripts/verify.py --paper 23 --check comparator --suite relative-main
```

Preparation expands the certificate-check source locally and checks its exact output hashes before installation. `prepare.py --paper 23` prints the plan; adding `--check` tests readiness. Source generation does not prove the certificate identities.

## Assumptions

`PrueScrimshawH2Input` supplies bijectivity of the actual inclusion-induced singular H₂ map under the internally proved graph conditions. `OrderedCubicalComparisonInput` includes the concrete cubical CW/chain adapter and cellular-to-singular comparison. Neither supplies a cycle, detector or torsion conclusion. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

End-to-end source generation, the complete current build and axiom audit, and the relative kernel replay require verification. The explicit witness is an alternative non-alternating certificate; the paper’s support counts, exact pivot-program refinement and rank-one integer witnesses are not reproduced. A K₃,₃ incidence embedding is proved, but a formal nonplanarity predicate/theorem is not supplied.

The unconditional declaration `P23MainResult.theorem_one` is absent from `Verification.MainSolutionSkeleton`. The `unconditional-probe` command with `--allow-diagnostic` checks that missing-export boundary; it does not validate the conditional theorem. The `auxiliary` comparison checks certificate algebra and cubical identities only.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/OGT-order_six_torsion_in_an_ordered_graph_configuration_space.pdf).
- [Prue–Scrimshaw, Abrams’s stable equivalence for graph braid groups](https://arxiv.org/abs/0909.5511).
- [Hatcher, Algebraic Topology, homotopy invariance and cellular homology](https://pi.math.cornell.edu/~hatcher/AT/AT..pdf).
