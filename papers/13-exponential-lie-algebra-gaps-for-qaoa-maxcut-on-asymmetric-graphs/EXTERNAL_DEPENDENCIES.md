# External dependencies

There are no registered mathematical exemptions. The QAOA operator/dimension classification associated with Kazi et al. and Kokcu et al. is reconstructed in Lean as graphMa_eq_scSpace_of_nonbip and graphMa_dimension_of_nonbip; it is not an assumed external theorem. All certificates are actual Lean matrix constructions and finite proofs, with no missing external data files. StatementContracts/Challenge.lean has 24 specification-only sorry placeholders outside the production root. The two independent control modules deliberately test type and axiom rejection on a small True target. Historical acceptance used official Comparator 97ef939c9fe3f8abf93e4adb654517476da7a66f. The duplicate genuine FullChallenge wrapper had no fixed official endpoint and was omitted from this release; StatementContracts/Solution.lean preserves all 24 genuine contracts.

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
