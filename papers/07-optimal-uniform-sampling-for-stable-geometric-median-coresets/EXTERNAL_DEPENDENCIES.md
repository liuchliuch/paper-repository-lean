# External dependencies

No paper-specific external theorem exemption is used. The project proves the actual Gaussian/Lebesgue L2 embedding rather than assuming it. Corollary 4.1 retains the source’s attained-median hypothesis; approximate-reference and nonattainment results have separate explicit scalar conditions. Sampling is the actual uniform law on m-subsets, not independent sampling substituted for it. The lower proof chooses a larger admissible population n>=20*m² to use a coarser collision bound while preserving the original sample constant and 2/5 failure. Proposition A.1 is proved from a stronger local theorem, without claiming to duplicate its alternative martingale proof.

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
