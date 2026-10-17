# External dependencies

Lean is pinned by `lean-toolchain` to `leanprover/lean4:v4.24.0`. Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` in the Lake configuration and `lake-manifest.json`; all transitive packages retain exact commit revisions in the manifest. Preserve these pins and use the repository shared tooling.

Nine external categories are retained in the detailed [EXTERNAL_INPUTS.md](EXTERNAL_INPUTS.md):

- E1–E2: the actual iid finite-categorical method-of-types KL inequality and Weissman TV inequality, exposed through `Paper36.RowTapes.ExternalCategoricalConcentration`. Arbitrary priors, adaptive tapes, count prefixes, posterior transfer and performance are local deductions.
- E3: a labelled comparison sorter with one uniform cost contract for every key vector, consumed by `CalibrationScan`; the CVaR scan, dynamic program and its cost composition are local.
- E9: `Paper36.Selection.CompactSectionMaximum`, a generic measurable maximizer for a Borel graph with nonempty compact Polish sections and a measurable/section-continuous objective. The actual policy feasible graph, compactness, strict-feasibility instantiation and Borel oracles are local.
- E4–E8: positive binary Subset Sum hardness, short rational polytope witnesses, existential-real decision in PSPACE, exact real-algebraic decision/optimization, and standard binary arithmetic/serialization composition. These are documented narrative class-transfer boundaries. The source-specific reductions, coefficient/monomial/payload bounds and exact semantic equivalences are Lean source. No literal Lean NP-completeness, PSPACE predicate or machine encoder is claimed.

The posterior-copy `BayesLaw`, original prior, Borel oracle and selected-policy execution identities specify the source algorithm. They are separate from published theorem inputs. Actual conditional physical dynamics and unused-tape freshness are proved from the native process, not added performance assumptions. Signed debt is not positive-part/per-episode safety. The fixed `(K,delta)` risk certificate is not a confidence sequence.

No added production axiom or registered external `sorry` is used. There are no compile-time certificate assets. The two missing leaf artifacts and final aggregate are still pending compilation.

Official Comparator uses the repository shared pinned installation. Challenge modules intentionally contain proof placeholders to specify fixed expected theorem types. They and deliberate negative-control axioms are verification fixtures, outside the production build target. The production proof closure must be checked independently of those fixtures.
