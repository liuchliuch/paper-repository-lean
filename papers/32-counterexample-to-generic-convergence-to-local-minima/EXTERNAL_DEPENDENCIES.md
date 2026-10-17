# External dependencies

Lean is pinned by `lean-toolchain` to `leanprover/lean4:v4.24.0`. Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7` in the Lake configuration and `lake-manifest.json`; all transitive packages retain exact commit revisions in the manifest. Preserve these pins and use the repository shared tooling.

No paper-specific external theorem assumptions or registered external `sorry` declarations are used. The Davis–Drusvyatskiy–Jiang (DDJ) framework is background correspondence: the measurable oracle, conditional noise moment and step assumptions are proved in `Paper32/DDJBridge.lean`; an external DDJ convergence theorem is not a premise. Ordinary foundational axioms permitted by Comparator are `propext`, `Classical.choice`, and `Quot.sound`. There are no certificate/data assets needed at compile time.

Official Comparator uses the repository shared pinned installation. Challenge modules intentionally contain proof placeholders to specify fixed expected theorem types. They and deliberate negative-control axioms are verification fixtures, outside the production build target. The production proof closure must be checked independently of those fixtures.
