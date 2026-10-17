# Minimax estimation of the pseudo-spectral gap at arbitrary relative precision

[Source paper](https://liuchliuch.github.io/repository/minimax-estimation-of-the-pseudo-spectral-gap-at-arbitrary-relative-precision/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1 | `P21Contract.theorem_1` | Uniform relative-error estimation from an arbitrary initial law for finite irreducible aperiodic chains, using gammaHat and the stated sample bound with C ≥ 73728. |
| Theorem 2 | `P21Contract.theorem_2` | Minimax sample bounds on the exact source model class for d ≥ 2, 0 < p ≤ 1/d, 0 < g ≤ 1/8 and 0 < ε < 1/2, with constants 1/2048 and 73729. |
| Lemma 1 | `P21Contract.lemma_1` | Gap-of-powers bounds and the associated contraction consequence for the stationary law. |
| Proposition 1 | `PsgEst.Paper.proposition_1` | Concentration of the actual empirical relative Laplacian with the source constants. |
| Lemma 2 | `PsgEst.Paper.lemma_2_paper` | Both visit-count bounds for arbitrary initial distributions and the explicitly defined blocking parameter. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/verify.py --paper 21 --check static
python3 ../../scripts/verify.py --paper 21 --check build
python3 ../../scripts/verify.py --paper 21 --check comparator --suite main
```

## Assumptions

The principal results have no remaining external concentration hypothesis: Paulin concentration and scalar/matrix Freedman are proved internally. See [External dependencies](EXTERNAL_DEPENDENCIES.md) for the factored interfaces and their scope.

## Verification

`Paper21` imports the `PsgEst` development, and `Verification` adds the statement proofs and axiom audit. Conditional concentration interfaces are discharged by internal theorems. The alternative h/k statistic is only factor-two equivalent to the pseudo-spectral gap; no equality is asserted for that alternative estimand.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/MPSG-minimax_estimation_of_the_pseudo_spectral_gap_at_arbitrary_relative_precision.pdf).
