# External dependencies

No mathematical external-dependency exemptions or known own mathematical gaps were registered at delivery. The finite-gap proof requires three binary assets under Paper15/CertificateData: forest.bin, representatives.bin, neighbours.bin. These are untrusted certificate data read by elaborators; the checked generators reconstruct ordinary Lean terms and use Lean.addDecl through kernel checking, rather than trusting native computation as a proof. The generated chunks remain proof requirements, reproduced locally from pinned source rather than versioned. `generated-artifacts.json` records the hashes, byte counts, module names, and imports of three binary inputs and 1,045 chunk modules. The hand-written checkers, two small elaboration entry points, and proof assembly modules remain in the source distribution. The original record reports 533 gap batches, 512 orbit batches, 61,871 gap traces with 5,103,027 nodes, and 1,670,544 neighbour transitions compiled, plus a 1,985,525-declaration permitted-axiom audit and rejected negative controls. Those are historical reports, not checks rerun for this release. Full 25-contract official positive kernel replay was interrupted/deferred by the user; final acceptance has not been obtained. Four final Challenge placeholders are isolated specifications and do not enter the production root.

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

Source-only certificate preparation requires Python 3, a native C++17 compiler supporting `__int128_t`, and Boost.Multiprecision headers (`cpp_int.hpp`, `int256_t`); Boost is header-only here. `CXX` selects one executable, default `c++`. Optional `BOOST_INCLUDEDIR` points to the directory containing `boost/`; compilation uses fixed `-O3 -std=c++17` flags without ambient `CXXFLAGS`. Python and the compiler target must both be little endian, enforced by explicit prechecks. The historical Appendix run used GCC 16.1.0; the Boost version was not recorded. All generator source files are SHA-256 pinned, and the exact hash gate rejects outputs that differ from the frozen release. No regeneration or compiler execution has been performed for this source-only export. The substantial preparation computation is a separate manual action and is never launched implicitly by a build.
