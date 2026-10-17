# Sharp Rank Laws for Maxout Switch Density

Source: [paper](https://liuchliuch.github.io/repository/rank-linear-knot-density-for-maxout/).

## Results

The entry module is `Paper35.lean`. Switches are defined from actual active candidates and counted with their parameter multiplicity.

| Source result | Lean declaration | Scope |
| --- | --- | --- |
| Theorem 2.3 | `Paper35.SourceTheorems.theorem_2_3_spectral` | Weighted iid visibility/covariance bound under the conditional-density and moment hypotheses. |
| Corollary 2.5 | `Paper35.SourceSupremum.universal_rank_linear_coefficient_iff` | Sharp universal rank-linear coefficient, including a positive-length shrinking-segment construction. |
| Theorem 2.8 | `Paper35.GaussianLift.jointlyGaussian_spherical_length` | Jointly Gaussian spherical-length law, relative to the named classical Gaussian, Crofton and calculus inputs. |
| Theorem 8.1 | `Paper35.DeepModel.Network.source_network_switch_bound_original` | Switch propagation through independently composed layers. |
| Proposition 8.2 | `Paper35.GaussianWinner.GaussianUnit.winner_secondMoment_standard` | Selected active-weight second moment under the explicit Gaussian law/regression inputs. |

The development also treats heterogeneous candidates, random probes, anisotropic Gaussian parameters, rank asymptotics and deep Gaussian networks.

## Build

Run the static check from this directory:

```sh
python3 ../../scripts/verify.py --paper 35 --check static
```

Prepare the full theorem contracts before comparing the source results:

```sh
python3 scripts/prepare-full-contracts.py prepare
```

Preparation builds `Paper35`, exports theorem types and writes explicit contracts under `Verification/FullDelivery/`. Independently compare every generated type with the source anchors in `Verification/full-targets.json` and the interfaces in `external-inputs.json`, checking hypotheses and quantifier order. Type export alone does not establish this correspondence.

After that review, use the exact manifest SHA256 printed by preparation:

```sh
python3 scripts/prepare-full-contracts.py check-reviewed REVIEWED_SHA256
python3 ../../scripts/verify.py --paper 35 --check comparator --suite full --reviewed-manifest-sha256 REVIEWED_SHA256
python3 ../../scripts/verify.py --paper 35 --check comparator --suite full-negative-added-premise --reviewed-manifest-sha256 REVIEWED_SHA256
python3 ../../scripts/verify.py --paper 35 --check comparator --suite full-negative-illegal-axiom --reviewed-manifest-sha256 REVIEWED_SHA256
```

Each comparison first checks the reviewed manifest and unchanged input/fixture hashes. The hash check does not perform semantic review. Preparation refuses to overwrite generated outputs; inspect changed inputs before regenerating and repeat the review.

For a production build alone, use:

```sh
python3 ../../scripts/verify.py --paper 35 --check build
```

## Assumptions

Lean and Mathlib are pinned in the project files. Classical Borel enumeration/projection, Crofton, Gaussian distribution/regression, curve calculus, extreme-value and convex-geometric interfaces remain explicit theorem parameters. Their exact statements, references and use sites are in [external dependencies](EXTERNAL_DEPENDENCIES.md) and [the interface registry](external-inputs.json). No supplied interface assumes the Maxout visibility bound, sharpness limit, selected-winner expansion or network recursion.

## Verification

The full contracts have not been generated or independently reviewed, and the final aggregate build, official comparison, complete axiom audit and fresh replay remain incomplete. The existing `subset` comparator checks supporting results only and cannot establish the complete source scope. Full negative controls must reject an added premise and an unauthorized axiom. The exporter may require repair when first compiled; its presence is not a compilation result.

## References

- [Source-to-declaration map](Verification/full-targets.json).
- [Classical theorem statements and bibliography](external-inputs.json).
