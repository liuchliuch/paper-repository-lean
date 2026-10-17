# Galois-modular extensions for Tannakian centers with prescribed spherical structure

[Source paper](https://liuchliuch.github.io/repository/galois-modular-extensions-for-tannakian-centers-with-prescribed-spherical-structure/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1 | `Paper18.Category.CategoricalTheorem11.exists_modularExtension` | A fully faithful braided spherical embedding into a modular fusion category with integral centralizer, preserving the prescribed spherical structure, relative to the explicit JF23 and ENO inputs. |
| Lemma A.1 | `Paper18.Category.FixedBoundary.MinimalExistence.lemmaA1_relative_to_ENO_at_center` | ENO-relative existence of a minimal extension, together with the universal classification retaining the specified boundary comparison. |
| Proposition 2.2 | `Paper18.Category.FixedBoundary.MinimalExistence.proposition2_2_relative_to_ENO` | Prescribed spherical enhancement for every minimal extension with the negative-dimensional C₂ generator; existence is relative to ENO realization. |
| Lemma 2.1 | `Paper18.Category.lemma2_1` | The actual categorical existence, uniqueness and inverse-twist assertion. |
| Lemma 3.1 | `P18Category.equivariant` | Integrality of an actual equivariant category is equivalent to integrality of its source; dominant-functor and Frobenius–Perron dimension results are also provided. |
| Appendix B | `P18Original.appendixB` | The pointed obstruction, quantified over all spherical structures on the fixed ambient category. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/verify.py --paper 18 --check static
python3 ../../scripts/verify.py --paper 18 --check build
python3 ../../scripts/verify.py --paper 18 --check comparator --suite relative-full
```

## Assumptions

The main theorem takes Johnson–Freyd Proposition 2.3 at two compatible presentation sizes and the ENO fixed-action fourth-obstruction realization result as explicit proposition parameters. Neither has a supplied inhabitant. Prescribed spherical compatibility, fixed-boundary classification and integrality deductions are internal. The secondary Galois-orbit consequence is not formalized. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

`Paper18` exposes the categorical results and `Verification.FinalAxiomAudit` checks their axiom closure. The `relative-full` comparison retains the external parameters in the theorem types. The algebraic `core` and numerical `conditional` comparisons concern supporting reductions and do not assert the unconditional categorical existence theorem.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/GME-galois_modular_extensions_for_tannakian_centers_with_prescribed_spherical_structure.pdf).
- [Johnson–Freyd, Schopieray’s Galois-modular extension conjecture, Proposition 2.3](https://arxiv.org/abs/2601.23192v1).
- [Etingof–Nikshych–Ostrik, Fusion categories and homotopy theory](https://arxiv.org/abs/0909.3140).
