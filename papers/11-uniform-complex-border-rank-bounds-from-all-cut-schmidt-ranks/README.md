# Uniform complex border-rank bounds from all-cut Schmidt ranks

[Source paper](https://liuchliuch.github.io/repository/uniform-complex-border-rank-bounds-from-all-cut-schmidt-ranks/).

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1.1 | `UniformBorderRank.Paper.theorem_1_1` | The maximum all-cut Schmidt rank gives the original explicit complex border-rank bound for nonzero finite tensors of order at least two, including the rank-one product branch. |
| Corollary 1.2 | `UniformBorderRank.Paper.corollary_1_2` | A bound D on all nontrivial cut ranks implies membership in the projective Segre secant of index Bhat D. |
| Proposition 2.2 | `UniformBorderRank.Paper.proposition_2_2` | Constructs the original anchored matrix-product representation and coefficient reconstruction. |
| Equation (18) | `UniformBorderRank.Paper.full_derivative_dimension` | The dimension of the actual iterated partial-derivative space equals the sum of all cut Schmidt ranks. |

## Build

Use `leanprover/lean4:v4.29.0-rc6` and the pinned `lake-manifest.json`. Run these commands from this paper directory.

```sh
python3 ../../scripts/verify.py --paper 11 --check static
python3 ../../scripts/verify.py --paper 11 --check build
python3 ../../scripts/verify.py --paper 11 --check comparator --suite main --local
```

## Assumptions

The main tensor bounds use their explicit finite-dimensional complex tensor and rank hypotheses. Full Corollary 5.1 additionally needs global scheme-theoretic Segre chart and span identifications that are not formalized here. The W-state exact-rank comparison, Nisan’s optimal ABP prefix-width characterization, and the Bhargava–Tengse commutative ABP construction also remain external secondary results. See [external dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

This project requires `leanprover/lean4:v4.29.0-rc6` and its matching pinned Comparator/exporter profile. Import `UniformBorderRank` and `Paper.Proofs` for the library and public theorem wrappers. [comparator/config.json](comparator/config.json) compares the explicit propositions in `Paper/Statements.lean` against the proved endpoints.

The Comparator requires the matching pinned shared tools described in the [repository instructions](../../README.md). The displayed `--local` command runs trusted sources without an operating-system sandbox. Positive checks permit `propext`, `Classical.choice`, and `Quot.sound`.

## References

- [Uniform complex border-rank bounds from all-cut Schmidt ranks](https://liuchliuch.github.io/repository/uniform-complex-border-rank-bounds-from-all-cut-schmidt-ranks/).
- N. Nisan, *Lower bounds for non-commutative computation*, STOC 1991. [DOI](https://doi.org/10.1145/103418.103462).
- V. Bhargava and A. Tengse, *Explicit Commutative ROABPs from Partial Derivatives*, FSTTCS 2024. [Paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.FSTTCS.2024.10).
- [Stacks Project: Segre embeddings](https://stacks.math.columbia.edu/tag/01WD).
