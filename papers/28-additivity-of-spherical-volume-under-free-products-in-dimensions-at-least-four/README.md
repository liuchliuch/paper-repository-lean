# Additivity of spherical volume under free products in dimensions at least four

Lean formalization of [the source paper](https://liuchliuch.github.io/repository/additivity-of-spherical-volume-under-free-products-in-dimensions-at-least-four/). Entry point: [`Paper28.lean`](Paper28.lean).

## Results

| Source result | Lean declaration | Mathematical scope |
| --- | --- | --- |
| Theorem 1.1 | `Paper28.theorem_1_1` | Spherical-volume additivity for integer classes of countable free-product groups in every dimension n = k + 4, using current-mass infima. |
| Corollary 1.2 | `Paper28.corollary_1_2` | Connected-sum additivity for closed connected oriented topological manifolds in dimension at least four, through their fundamental-group classes. |
| Lemma 2.1 | `Paper28.lemma_2_1` | The two norm-folding approximate-tangent Jacobians sum to at most one, mass-almost-everywhere, for n ≥ 4, including zero strata. |
| Definition 2.2 | `Paper28.sphereVertexShadow` | The incident-edge vertex shadow on the unit sphere; branch routing agrees with deleted-vertex connectivity independently of endpoint choice. |
| Lemma 2.3 | `Paper28.lemma_2_3` | The joint Jacobian bound for all vertex shadows of a finite tree, mass-almost-everywhere, for n ≥ 4. |
| Lemma 3.1 | `Paper28.lemma_3_1` | Positive-degree quotient cycles admit homologous polyhedral approximations with arbitrarily small excess mass and exact prescribed polyhedral fillings. |
| Proposition 3.2 | `Paper28.proposition_3_2` | Integer Bass–Serre transfers are well defined, commute with boundary and satisfy the joint mass bound in dimensions at least four. |
| Lemma 5.1 | `Paper28.lemma_5_1` | Near-isometric deformation of a compact carrier, fixing the prescribed polyhedral support, with a compact-image Lipschitz homotopy. |
| Lemma 5.2 | `Paper28.lemma_5_2` | Sharp mass approximation on finite spherical polyhedra, homologous fillings of vanishing mass, and exact prescribed polyhedral fillings. |

## Build

Run from this directory with Python 3.11+, Git and Lean installed through elan. The committed `lean-toolchain` and `lake-manifest.json` select the compiler and dependency revisions.

```sh
python3 ../../scripts/verify.py --paper 28 --check static
python3 ../../scripts/verify.py --paper 28 --check build
python3 ../../scripts/verify.py --paper 28 --check comparator --suite main
```

## Assumptions

The regular Hilbert sphere, action and orbit quotient are constructed in Lean. Canonical round metrics, AK/FF currents and integration, group homology and Song comparison, generic PL realization/transport, homology comparison, measure facts, linear algebra, Bass–Serre structure and connected-sum topology remain explicit foundation inputs. Their exact scopes are in [EXTERNAL_DEPENDENCIES.md](EXTERNAL_DEPENDENCIES.md).

## Verification

The theorem statements retain the external object and compatibility parameters; checking them does not construct closed AK/current, homology or topology witnesses. The inputs do not assert the paper’s approximation, filling, transfer-recovery, joint-mass or additivity conclusions. Connected-sum topology supplies only the free-product and fundamental-class pinch identities. See [verification prerequisites](../../docs/verification.md).

## References

- [Ambrosio–Kirchheim, Currents in metric spaces](https://doi.org/10.1007/BF02392711).
- [Song, Spherical volume and spherical Plateau problem](https://arxiv.org/pdf/2202.10636v6).
- [Riedweg–Schäppi, current-homology comparison](https://arxiv.org/pdf/0902.3831).
- [Rourke–Sanderson, Introduction to Piecewise-Linear Topology](https://webhomes.maths.ed.ac.uk/~v1ranick/papers/rsplx.pdf).
