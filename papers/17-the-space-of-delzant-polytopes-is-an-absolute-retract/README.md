# The space of Delzant polytopes is an absolute retract

[Source paper](https://liuchliuch.github.io/repository/the-space-of-delzant-polytopes-is-an-absolute-retract/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.2 | `P17Contract.theorem_1_2_euclidean` | Absolute extensor and absolute retract properties for Delzant polytopes with the Euclidean Hausdorff metric, including open convex support restrictions and controlled extensions. |
| Theorem 1.2, volume metric | `P17Contract.theorem_1_2_volume` | The corresponding result for Lebesgue volume of symmetric difference, with a proved identity homeomorphism between the metric topologies. |
| Lemma 2.2 | `Paper17.exists_delzant_refinement_of_rational_normal` | Smooth projective refinement of rational polytopal normal fans. |
| Example 2.4 | `Paper17.Example24.source_example_2_4` | The triangle counterexample, its fan geometry, the hexagonal refinement and the prism perturbation with exact Hausdorff error. |
| Proposition 4.3 | `P17Contract.proposition_4_3_euclidean` | Continuous approximation with arbitrary continuous positive error and locally finite normal fans. |
| Theorem 4.4 | `P17Contract.theorem_4_4_euclidean` | A jointly continuous deformation that is the identity at time zero and Delzant at positive times, with error less than the time parameter. |
| Appendix A | `P17Contract.QuantitativeDisk.quantitative_disk_filling` | Quantitative disk filling for actual loops and the closed complex disk. |

## Build

Lean 4.24.0 and the dependencies in `lake-manifest.json` are pinned. Run from this paper directory:

```sh
python3 ../../scripts/verify.py --paper 17 --check static
python3 ../../scripts/verify.py --paper 17 --check build
python3 ../../scripts/verify.py --paper 17 --check comparator --suite main
python3 ../../scripts/verify.py --paper 17 --check comparator --suite source
```

## Assumptions

The polytope, fan, metric and extension results have no additional mathematical hypotheses beyond their Lean statements. The symplectic toric-moduli application and the interpretation by toric birational morphisms require external classification and toric-variety theory; these applications are not formalized. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

`Paper17` contains the geometric development; `Verification` includes its statement proofs and axiom audits. The `main` and `source` comparisons cover complementary statements. The Appendix A proof uses compatible covers; it does not construct the paper’s particular annular triangulation.

## References

- [Main paper (PDF)](https://liuchliuch.github.io/files/repository/DAR-the_space_of_delzant_polytopes_is_an_absolute_retract.pdf).
