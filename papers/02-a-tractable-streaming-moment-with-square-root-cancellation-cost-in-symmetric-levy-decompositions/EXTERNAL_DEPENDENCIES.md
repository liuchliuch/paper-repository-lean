# External dependencies

The main theorem uses no paper-specific external axiom. Three consequences remain outside the formalized scope: (1) Proposition B.2 and (2) Proposition B.3 use the general complete-Bernstein/Pick analytic characterization to obtain a positive Bernstein Lévy–Khintchine representing measure, as in Schilling–Song–Vondraček, *Bernstein Functions*, second edition (2012), Chapters 3 and 6, DOI 10.1515/9783110269338. The paper-specific analytic kernels, finite-difference identities, approximation estimates and cost bounds are proved. Subordination from an explicitly supplied positive representation is also proved; the representation bridge itself is not. (3) Lemma A.1 does not formalize the ancillary O(r³) finite-field Gaussian-elimination runtime theorem (Håstad, *Advanced Algorithms*, §2.1.2, Theorem 2.4, https://www.csc.kth.se/~johanh/algnotes.pdf). Recovery correctness, dense rejection, actual halting enumeration, and O(K² log q) total decoder workspace remain proved. These were narrowly accepted historical scope exemptions, not proof axioms or blanket exemptions for the entire results.

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

The shared official Comparator is pinned by the monorepo tooling. Its allowed axioms are recorded separately in each fixed configuration. Challenge placeholders and intentionally invalid negative controls are verification fixtures and are excluded from the production entry.
