# External dependencies

Corollary 3.6 is not proved or asserted as a full result. It depends on Bavarian–Shor, Theorem 1.3, the stronger finite-field CHSH incidence estimate omega_r <= C0*r^(-1/2-epsilon): *Information causality, Szemerédi–Trotter and algebraic variants of CHSH*, ITCS 2015, DOI 10.1145/2688073.2688112, arXiv:1311.5186 (https://arxiv.org/html/1311.5186v2). The retained improved_polynomial_exponent and cor_3_6_constants prove only the elementary consequences for exponents and constants. No external theorem is inserted as an axiom or hidden assumption. All eight other numbered results, actual two-site law, nonidentical Borel-mixture lower bounds and optimal-error zero limit remain proved. KL is EReal and takes +infinity on support mismatch; full support and finite mixing support are not imposed to bypass that boundary.

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
