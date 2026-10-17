# External dependencies

The source Assumption 1.1 (surface-slow pure boxes) is a mathematical hypothesis of the main theorem, not a proved low-temperature result. Strong Gaussian disorder is the source Assumption 1.2, with a proved large-variance threshold. The acceptance record exempts the unconditional low-temperature Corollary 1.4: it requires Alexander Theorem 1.1(ii), a fixed-boundary two-dimensional Ising gap estimate. That theorem is not inserted as an axiom and is not silently claimed as a proved corollary. The official Comparator revision recorded in the original acceptance is 97ef939c9fe3f8abf93e4adb654517476da7a66f. There are no production certificate files, compile-time file inclusions, or nonstandard production axioms.

Lean toolchain: `leanprover/lean4:v4.24.0`.

Locked package revisions:

- `mathlib`: `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.
- `plausible`: `dfd06ebfe8d0e8fa7faba9cb5e5a2e74e7bd2805`.
- `LeanSearchClient`: `99657ad92e23804e279f77ea6dbdeebaa1317b98`.
- `importGraph`: `d768126816be17600904726ca7976b185786e6b9`.
- `proofwidgets`: `556caed0eadb7901e068131d1be208dd907d07a2`.
- `aesop`: `725ac8cd67acd70a7beaf47c3725e23484c1ef50`.
- `Qq`: `dea6a3361fa36d5a13f87333dc506ada582e025c`.
- `batteries`: `8da40b72fece29b7d3fe3d768bac4c8910ce9bee`.
- `Cli`: `91c18fa62838ad0ab7384c03c9684d99d306e1da`.

Only the standard logical axioms `propext`, `Classical.choice`, and `Quot.sound` are permitted by the positive official Comparator contracts unless a contract and the documented mathematical boundary explicitly say otherwise. An illegal axiom in a negative control is intentional and is never part of the production import.

Release verification status: static inspection only. No fresh build, certificate evaluation, full proof replay, or official Comparator run was performed for this export.
