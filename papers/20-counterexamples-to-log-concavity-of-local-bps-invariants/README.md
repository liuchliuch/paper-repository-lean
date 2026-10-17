# Counterexamples to log-concavity of local BPS invariants

[Source paper](https://liuchliuch.github.io/repository/counterexamples-to-log-concavity-of-local-bps-invariants/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1 | `Paper20.Counterexample43.theorem1_1` | Exact executable rank-43 BPS coefficients, the strict quantitative failure of log-concavity, and positivity of every required coefficient. |
| Theorem 1.2 | `Paper20.Counterexample36.theorem1_2` | Failure of log-concavity at indices 20/21/22 for every k ≥ 10, with all-coefficient positivity, relative to MathasInputs and the concrete finite certificate. |
| Proposition 3.1 | `P20Relative.prop_3_1` | The same constructed polynomial Q has the stated degree, evaluation at k(k+1), and values at zero, relative to MathasInputs. |
| Proposition 3.2 | `P20Relative.prop_3_2` | Its leading coefficient is the cardinal of genuine transposition returns divided by the factorial, relative to the stated character-theory inputs. |
| Geometric BPS coefficients | `P20Relative.geometric_program` | Signed integer extraction from supplied Euler data agrees with the executable coefficients, relative to the explicit geometric and character-theory inputs. |
| Normalized ruling | `P20Relative.ruling_polynomial_unique` | Faithful evaluation identifies the unique normalized ruling polynomial. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/prepare.py --paper 20 --execute
python3 ../../scripts/verify.py --paper 20 --check static
python3 ../../scripts/verify.py --paper 20 --check build
python3 ../../scripts/verify.py --paper 20 --check comparator --suite relative
```

Preparation expands the certificate-check source locally and checks its exact output hashes before installation. `prepare.py --paper 20` prints the plan; adding `--check` tests readiness. Source generation does not prove the certificate identities.

## Assumptions

MathasInputs supplies the Schur trace decomposition and full-twist eigenvalues on the actual Hecke representations. GeometricData/GeometricInputs supplies interpreted Hilbert, HOMFLY and ruling data with the published identities; those geometric objects are not constructed in Lean. The BPS/program equality, sign conversion, polynomial identities and finite computations are internal obligations. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

End-to-end source generation, the rank-36 `RContent36.All` root assembly, concrete final exports, complete axiom audit and full relative comparison require verification. The finite root is this project’s own calculation, not an external assumption.

The stricter unconditional interface is incomplete: `P20Required.thm_1_2`, `P20Required.lemma_2_2`, `P20Required.prop_3_1` and `P20Required.prop_3_2` are absent. The `unconditional-probe` command with `--allow-diagnostic` checks this missing-export boundary; it is not a positive proof check. The `supporting` comparison covers supporting computations only.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/LBPS-counterexamples_to_log_concavity_of_local_bps_invariants.pdf).
- [Mathas, Matrix units and generic degrees for the Ariki–Koike algebras](https://arxiv.org/abs/math/0108164).
- [Maulik, Stable pairs and the HOMFLY polynomial](https://arxiv.org/abs/1210.6323).
- [Rutherford, The Bennequin number, Kauffman polynomial, and ruling invariants](https://arxiv.org/abs/math/0511097).
