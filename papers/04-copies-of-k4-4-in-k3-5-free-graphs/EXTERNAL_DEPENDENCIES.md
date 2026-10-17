# External dependencies

All ten numbered results and the retained preliminary/construction claims use no paper-specific external axiom. The secondary introduction combination extending cubic order to all fixed t>=4 when s=3 is outside the formalized scope: it imports Wang–Yang–Zhou, *On the generalized Turán number of the complete bipartite graph K_{3,b+1}*, Theorem 1.1, arXiv:2607.01680v1 (2026), reference [5] of the source. The original paper explicitly uses that theorem for b>=5 and 4<=a<=b, whereas this project proves its own missing b=4 case. Only that external combination is exempt; it is neither a production axiom nor a waiver for the numbered results.

## Pinned software

The project uses `leanprover/lean4:v4.24.0`. The committed Lake manifest locks the following Git revisions; retain it when preparing the environment.

| Package | Revision |
| --- | --- |
| `mathlib` | `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` |
| `plausible` | `dfd06ebfe8d0e8fa7faba9cb5e5a2e74e7bd2805` |
| `LeanSearchClient` | `99657ad92e23804e279f77ea6dbdeebaa1317b98` |
| `importGraph` | `d768126816be17600904726ca7976b185786e6b9` |
| `proofwidgets` | `556caed0eadb7901e068131d1be208dd907d07a2` |
| `aesop` | `725ac8cd67acd70a7beaf47c3725e23484c1ef50` |
| `Qq` | `dea6a3361fa36d5a13f87333dc506ada582e025c` |
| `batteries` | `8da40b72fece29b7d3fe3d768bac4c8910ce9bee` |
| `Cli` | `91c18fa62838ad0ab7384c03c9684d99d306e1da` |

The shared official Comparator is pinned by the monorepo tooling. Its allowed axioms are recorded separately in each fixed configuration. Challenge statements and intentionally invalid negative controls are verification fixtures and are excluded from the production entry.
