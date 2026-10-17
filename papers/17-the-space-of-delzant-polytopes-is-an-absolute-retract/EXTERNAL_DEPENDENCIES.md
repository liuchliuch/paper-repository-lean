# External dependencies and scope

Mathlib is pinned to `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`; Lean is 4.24.0. Production proofs use only the standard permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.

Two accepted secondary exemptions remain unproved: (1) Corollary 5.1 transports the results to symplectic toric moduli using Atiyah and Guillemin–Sternberg moment-map convexity and Delzant classification/construction; actual Hamiltonian actions, symplectic reduction, and the specified-moment-map correspondence are unavailable. (2) The unnumbered S 5. p 5 interpretation of rational fan refinements/stellar subdivisions as proper toric birational morphisms/modifications depends on external toric-variety theory, as in Cox–Little–Schenck. Neither application is represented by a production axiom or counted as proved. All paper-owned polytope, metric, topology and Appendix A contributions remain in scope.

The shared release tooling installs the pinned official Comparator. Comparator challenge modules may contain specification placeholders; these are isolated from production proofs. Negative controls intentionally contain an added premise or an illegal axiom and are verification fixtures. No new axioms or proof placeholders were introduced by release curation.
