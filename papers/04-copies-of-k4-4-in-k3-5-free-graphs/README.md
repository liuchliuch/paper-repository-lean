# Copies of K₄,₄ in K₃,₅-free graphs

[Source paper](https://liuchliuch.github.io/repository/copies-of-k4-4-in-k3-5-free-graphs/).

Lean formalization of the finite-field construction and cubic extremal count for copies of K₄,₄ in K₃,₅-free graphs. The production entry is `K44K35Free.lean`.

## Results

| Source result | Public Lean declaration | Scope |
| --- | --- | --- |
| Theorem 1 | `K44K35Free.theorem_1` | For every sufficiently large n, a bipartite K₃,₅-free graph on n vertices has at least c*n³ unoriented K₄,₄ copies; `theorem_1_theta` gives the two-sided extremal bound. |
| Lemma 2 | `K44K35Free.lemma_2` | The actual unoriented copy count satisfies 8*numK44 ≤ choose(n,3). |
| Lemma 3 | `K44K35Free.lemma_3_projective` | Any three distinct cap points have linearly independent homogeneous vectors under the stated nonsquare-field hypothesis. |
| Proposition 4; Remark 5 | `K44K35Free.proposition_4` | Concrete plane sections, exact exceptional-family counts and incidences; `remark_5` gives the point-deletion obstruction. |
| Lemma 6 | `K44K35Free.lemma_6` | Monic quartic witnesses yield many nonexceptional four-point planes with an explicit positive constant and threshold. |
| Lemmas 7–8 | `K44K35Free.lemma_7` | Designated copies through an edge inject into the relevant Grassmannian; `lemma_7_bound` gives the 6*q⁴ estimate, and `lemma_8` bounds controlled-plane intersections. |
| Propositions 9–10 | `K44K35Free.proposition_10` | `proposition_9` excludes K₃,₅ for every valid simultaneous pruning outcome; the finite independent choice space gives the stated copy-survival bound. |
| Preliminary alteration and copy counting | `K44K35Free.preliminary_lower_bound` | Joint pairing selection and preliminary survival; `designated_copies_le_graph_copies` proves distinct designated pairs yield distinct graph copies. |

## Build

Install Python 3.11 or newer, Git, and Lean/Lake through elan. Run from this paper directory; the committed toolchain and Lake manifest select the dependencies.

```sh
python3 ../../scripts/verify.py --paper 04 --check static
python3 ../../scripts/verify.py --paper 04 --check build
python3 ../../scripts/verify.py --paper 04 --check comparator --suite main
```

## Assumptions

The numbered results use no paper-specific external theorem axiom. The introduction’s further combination giving cubic order for all fixed t ≥ 4 when s = 3 uses Wang–Yang–Zhou, Theorem 1.1, and is outside this development’s proved scope. See [External dependencies](EXTERNAL_DEPENDENCIES.md).

## Verification

The contracts use actual finite-field geometry, finite choice spaces, unoriented graph copies, and the finite extremal maximum. The pruning and distinct-copy arguments are included in the main scope; the separate Wang–Yang–Zhou combination is not. The official Comparator requires the shared pinned tool profile and `landrun`; trusted local execution can explicitly use `--local`.

## References

- [Source paper](https://liuchliuch.github.io/repository/copies-of-k4-4-in-k3-5-free-graphs/).
- [Wang, Yang and Zhou, On the generalized Turán number of the complete bipartite graph K₃,ᵦ₊₁, Theorem 1.1](https://arxiv.org/abs/2607.01680).
