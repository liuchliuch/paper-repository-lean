import Paper18.Results.PF
import Paper18.Results.Integrality
import Paper18.Results.Lacabanne
import Paper18.Results.Prop22
import Paper18.Results.Theorem11
import Paper18.Results.AppendixA
import Paper18.Results.AppendixB
import Paper18.Results.CategoricalLacabanne
import Paper18.Results.CategoricalCaseOne
import Paper18.Results.CategoricalProp22
import Paper18.Results.CategoricalPivotalBoundary
import Paper18.Results.CategoricalCaseOneModules
import Paper18.Results.CategoricalSigns
import Paper18.Results.CategoricalProp22Boundary
import Paper18.Results.CategoricalCaseOneTannakian
import Paper18.Results.CategoricalCaseTwoPivotal
import Paper18.Results.CategoricalCentralizerTannakian
import Paper18.Results.CategoricalProp22Minimal
import Paper18.Results.CategoricalCaseOneAmbient
import Paper18.Results.CategoricalPreliminaryCentralizerSphericalized
import Paper18.Category.Main

import Paper18.Results.CategoricalCaseOneExtension
import Paper18.Results.CategoricalCaseTwoAmbient
import Paper18.Results.CategoricalPreliminaryCentralizer
import Paper18.Results.CategoricalPreliminaryCentralizerDimension
import Paper18.Results.CategoricalProp22C2
import Paper18.Category.FixedBoundaryMinimalExistenceENO
import Paper18.Results.CategoricalJohnsonFreydPositive
import Paper18.Results.CategoricalTheorem11
/-!
# Paper 18 Results — re-exports

Main contributions:

* `Paper18.Category.lemma2_1` — the actual original Lemma 2.1, including
  existence, uniqueness and the inverse-twist assertion
* `Paper18.lemma2_1_twist` and `Paper18.prop2_2` — auxiliary numerical
  reductions, not the complete original categorical statements
* `Paper18.Category.FiniteSemisimpleSkeleton.lemma3_1_dominant` — the
  actual-category dominant-functor assertion of Lemma 3.1
* `Paper18.lemma3_1_dominant` / `Paper18.equivariant_dim_integral` — its
  algebraic multiplicity counterparts
* `Paper18.Category.FixedBoundary.MinimalExistence.lemmaA1_relative_to_ENO_at_center`
  — actual minimal existence relative to precise ENO input, and internally
  proved universal specified-boundary classification
* `Paper18.Category.CategoricalTheorem11.exists_modularExtension`
  — the actual original main output relative to registered JF/ENO inputs
* Conditional numerical reductions in `Paper18.Results.Theorem11` remain
  supplementary; they are not used in place of the actual main theorem
* The full actual Appendix B pointed obstruction
-/
