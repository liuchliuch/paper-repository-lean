# External dependencies and scope

Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; Lean is 4.24.0. Production permits only `propext`, `Classical.choice`, and `Quot.sound`. The final source results have no registered external mathematical dependency or exempt required result.

`ExternalConcentrationInputs` and conditional theorem variants remain useful factored interfaces. They are discharged by internally proved Paulin, scalar Freedman and matrix Freedman theorems; retaining these interfaces does not turn the final unconditioned main theorems into relative results. The actual stationary weighted norm, multiplicative reversiblization spectrum, empirical counts and source model/minimax equivalences are proved. The alternative h/k statistic is only factor-two equivalent to the pseudo-spectral gap and is documented under its own meaningful contracts.

The shared release tooling installs the pinned official Comparator. Comparator challenge modules may contain specification placeholders; these are isolated from production proofs. Negative controls intentionally contain an added premise or an illegal axiom and are verification fixtures. No new axioms or proof placeholders were introduced by release curation.
