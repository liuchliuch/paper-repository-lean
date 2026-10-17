import Paper18.Fusion.Basic
import Paper18.Fusion.Pivotal
import Paper18.Fusion.Braided
import Paper18.Fusion.Grading
import Paper18.Fusion.Sphericalization
import Paper18.Results.Main

/-!
# Paper 18 entry point

Galois–modular extensions for Tannakian centers with prescribed spherical
structure.  See `README.md` for the module map and paper-to-Lean correspondence.

The original actual-category main output is
`Paper18.Category.CategoricalTheorem11.exists_modularExtension`. Its exact
published external JF/ENO existence inputs remain explicit; their types and
uses are registered in `EXTERNAL_DEPENDENCIES.md`. The prescribed
spherical enhancement, fixed-boundary classification, both integrality
branches, actual Lemmas 2.1/3.1 and Appendix B are real Lean proofs.
The old `theorem1_1_reduction` is a supplementary numerical reduction.
The release metadata distinguishes relative verification from the unproved
unconditional external existence assertions.
-/
