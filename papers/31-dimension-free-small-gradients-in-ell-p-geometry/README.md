# Dimension-Free Gradient-Norm Minimization in ℓₚ and Schatten-p Spaces

Lean formalization of [the source paper](https://liuchliuch.github.io/repository/dimension-free-small-gradients-in-ell-p-geometry/). Entry point: [`Paper31.lean`](Paper31.lean).

## Results

| Source result | Lean declaration | Mathematical scope |
| --- | --- | --- |
| Definition 1.1 | `P31.OracleModel.Protocol` | Deterministic exact-real query protocols count every executed oracle invocation, including repeated queries. |
| Theorem 1.2 | `P31.vector_upper_bound_uniform_constant` | The actual vector program achieves the dual-gradient target; one constant precedes dimension, scales and accuracy, including zero-query/easy cases. |
| Corollary 1.3 | `P31.LowerBound.corollary1_3_from_composite` | Conditional minimax comparison under the original simultaneous normalized hard-family Assumption 6.1, with actual oracle rescaling and appended output query. |
| Corollary 1.4 | `P31.Schatten.matrix_upper_bound_uniform_constant` | The rectangular Schatten analogue uses actual matrices, compact-SVD-pinned singular values, trace gradients and executed query counts. |
| Lemma 2.1 | `P31.powerAtom_hasFDerivAt` | Derivative and normalized shifted-power geometry, with dual-norm and radial identities and the explicit scalar Clarkson input. |
| Lemma 2.2 | `P31.lemma2_2` | Distance contraction and integer query budget from the objective-only complementary-composite guarantee and the normalized atom. |
| Lemmas 4.1–4.2 | `P31.stagewise_transport_and_contraction` / `P31.path_bound` | Regularized-minimizer transport, valid warm starts, stage contraction and the continuation path bound. |
| Remarks 5.1 and 5.3 | `P31.vector_weaker_target` / `P31.Schatten.matrix_stronger_target` | Alternate gradient-norm targets retain the correct query bounds; stronger targets incur the sharp dimension factor. |
| Corollary 5.2 | `P31.accuracy_oblivious_checkpoints` | A wrapper independent of target accuracy composes actual programs with geometric cumulative query cost and a zero-scale branch. |
| Lemma 6.2 | `P31.lemma6_2` | Objective-to-gradient localization for the hard family, with genuine Frechet derivatives and normalized rescaling. |
| Proposition 7.1 | `P31.QuadraticMetric.actual_query_proposition71` | For actual PSD quadratics, the constructed positive diagonal majorant and Hilbert routine give the source target; the zero operator uses no query. |

## Build

Run from this directory with Python 3.11+, Git and Lean installed through elan. The committed `lean-toolchain` and `lake-manifest.json` select the compiler and dependency revisions.

```sh
python3 ../../scripts/prepare.py --paper 31
python3 ../../scripts/prepare.py --paper 31 --execute
python3 ../../scripts/verify.py --paper 31 --check static
python3 ../../scripts/verify.py --paper 31 --check build
python3 ../../scripts/verify.py --paper 31 --check comparator --suite main
```

Preparation reconstructs fixed Comparator source from a literal independent statement template and text-edit recipes, checking exact output hashes. It does not extract statements from the current proofs.

## Assumptions

`P31.LowerBound.SimultaneousHardFamily` is the paper’s original Assumption 6.1, not an established external theorem or a consequence of separate literature constructions. Other explicit inputs are the objective-only complementary-composite engine, scalar Clarkson, raw rectangular spectral facts, Gaussian moments, SDP duality/attainment, norm duality and the Hilbert small-gradient routine. Exact prox operations and internal exact-real arithmetic are uncharged. [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md) specifies every boundary.

## Verification

The fixed statement template retains the external parameters and original conditional premise. Verifying its Lean proofs does not construct those witnesses or establish the simultaneous hard-family assumption. Spectral inputs are tied to genuine compact SVDs; Gaussian/SDP inputs supply standard facts rather than the numerical diagonal-majorant bound. See [verification prerequisites](../../docs/verification.md).

## References

- [Diakonikolas–Guzmán, complementary-composite acceleration](https://arxiv.org/html/2101.11041v2).
- [Kim–Park–Ozdaglar–Diakonikolas–Ryu, small-gradient methods](https://arxiv.org/html/2311.17296v2).
- [Ball–Carlen–Lieb, uniform convexity and smoothness of trace norms](https://doi.org/10.1007/BF01231769).
