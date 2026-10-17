# The Griffiths exponent of random-field Ising dynamics at strong Gaussian disorder

[Source paper](https://liuchliuch.github.io/repository/the-griffiths-exponent-of-random-field-ising-dynamics-at-strong-gaussian-disorder/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.3 | `Paper09.RFIM.theorem_1_3` | Simultaneous two-sided bounds for heat-bath relaxation and worst-start mixing times, and both truncated double-log limits in probability, for dimension d ≥ 2. |
| Proposition 2.1 | `Paper09.RFIM.proposition_2_1` | The Gaussian lower bound at every fixed positive variance under the surface-slow pure-box hypothesis. |
| General iid extension, §2 | `Paper09.RFIM.proposition_2_1_iid` | The lower bound for iid real fields satisfying the stated polynomial small-ball and two shell-tail conditions. |
| Corollary 1.4: exponent identity | `Paper09.aExp_two` | The identity (2 − 1)/2 = 1/2. The unconditional low-temperature corollary is not formalized. |

## Build

Use `leanprover/lean4:v4.24.0` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/verify.py --paper 09 --check static
python3 ../../scripts/verify.py --paper 09 --check build
python3 ../../scripts/verify.py --paper 09 --check comparator --suite main --local
```

## Assumptions

The main theorem assumes positive inverse temperature and variance, `SurfaceSlowPureBoxes` (Assumption 1.1), and `StrongGaussianDisorder` (Assumption 1.2). A sufficiently large Gaussian variance is proved to satisfy the disorder condition. The unconditional two-dimensional low-temperature corollary additionally needs Alexander’s Theorem 1.1(ii), which is not proved here. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

Import `Paper09` for the production library. The fixed statement and axiom checks use [Verification/comparator.json](Verification/comparator.json); the dimension-two contract covers the exponent identity only.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [The Griffiths exponent of random-field Ising dynamics at strong Gaussian disorder](https://liuchliuch.github.io/repository/the-griffiths-exponent-of-random-field-ising-dynamics-at-strong-gaussian-disorder/).
- K. S. Alexander, *The spectral gap of the 2-D stochastic Ising model with nearly single-spin boundary conditions*, J. Stat. Phys. 104 (2001), 59–87. [DOI](https://doi.org/10.1023/A:1010301525937).
