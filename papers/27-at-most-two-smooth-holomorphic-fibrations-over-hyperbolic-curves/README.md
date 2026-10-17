# At most two smooth holomorphic fibrations over hyperbolic curves

Lean formalization of [the source paper](https://liuchliuch.github.io/repository/at-most-two-smooth-holomorphic-fibrations-over-hyperbolic-curves/). Entry point: [`Paper27.lean`](Paper27.lean).

## Results

| Source result | Lean declaration | Mathematical scope |
| --- | --- | --- |
| Theorem 1.1 | `Paper27.Geometry.ClassicalInputs.at_most_two_classes` | A compact complex surface has at most two classes of smooth connected-fibre holomorphic fibrations over genus-at-least-two curves, up to base biholomorphism. |
| Corollary 1.2 | `Paper27.Geometry.at_most_two_kodaira` | The Kodaira-fibration bound, using the separate base-hyperbolicity theorem for non-isotrivial families. |
| Lemma 2.1 | `Paper27.Geometry.FibreGeometry.finitePair_pairSurjective` | Two inequivalent smooth fibrations give a finite surjective map to the product of their bases. |
| Lemma 2.2 | `Paper27.Geometry.LineBundleDegreeTheory.connection_degree_zero` | The classical zero-degree consequence of a holomorphic connection is an explicit general input. |
| Lemma 2.3 | `Paper27.Geometry.CurveBranchInputs.curve_metric_rigidity` | Equal derivative ramification divisors give equal pullback metrics and local isometry graphs, including ramified centres. |
| Proposition 2.4 | `Paper27.Geometry.ClassicalInputs.ramification_geometry` | Critical components carry cyclic normal charts, unramified restrictions, Jacobian order n−1 and negative normal-cocycle degree. |
| Remark 2.5 | `Paper27.Geometry.CheckingBothProjections.checking_both_projections` | The supplied Zaal construction has an actual nonsubmersive projection; no connected-component degree or connected second fibre is assumed. |
| Lemma 3.1 | `Paper27.Geometry.intrinsic_ramification_component_dichotomy` | A third fibration is disjoint from a critical component or shares its tangency, supporting the common-index construction. |
| Lemmas 3.2–3.3 | `Paper27.Geometry.ActualDisjointObstruction.impossible` / `Paper27.Geometry.ClassicalInputs.common_tangency_impossible_by_averaging` | The disjoint and common-tangency cases contradict negative normal degree, using actual splittings and cyclic averaging. |
| Lemma 3.4 | `Paper27.Geometry.unramified_pair_fibration_equivalent` | Every hyperbolic third fibration of a finite unramified product cover factors through one projection; it need not be smooth. |
| Sharpness | `Paper27.Geometry.product_exactly_two` / `Paper27.Geometry.double_kodaira_attains_bound` | Product projections attain the bound; the double-Kodaira example additionally uses the published existence input. |

## Build

Run from this directory with Python 3.11+, Git and Lean installed through elan. The committed `lean-toolchain` and `lake-manifest.json` select the compiler and dependency revisions.

```sh
python3 ../../scripts/verify.py --paper 27 --check static
python3 ../../scripts/verify.py --paper 27 --check build
python3 ../../scripts/verify.py --paper 27 --check comparator --suite paper
```

## Assumptions

The results take explicit universal curve-map, metric/uniformization, covering, local-analysis, bundle-degree and Bott inputs; the averaging argument has general analytic/bundle hypotheses. Their witnesses are not supplied as closed Lean constructions. Kodaira base hyperbolicity, double-Kodaira existence and the Zaal construction are separate inputs. [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md) records exact statements and source qualifications.

## Verification

Ramification is represented by the actual derivative critical support and transverse Jacobian orders in cyclic charts. Self-intersection is represented by the degree of the honest normal quotient cocycle. A separate global divisor/intersection-pairing theory is not implemented. The `paper` comparison checks these conditional geometric statements; it does not construct the universal external theories. See [verification prerequisites](../../docs/verification.md).

## References

- [Troyanov, Prescribing curvature on compact surfaces with conical singularities](https://sma.epfl.ch/~troyanov/Papers/Prescribing.pdf).
- [Forster, Lectures on Riemann Surfaces](https://www.mathematik.uni-muenchen.de/~forster/books/riem/riemsurf.html).
- [Catanese–Rollenske, Double Kodaira fibrations](https://arxiv.org/pdf/math/0611428).
