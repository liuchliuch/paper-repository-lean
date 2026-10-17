import Paper17.Basic
import Paper17.Support
import Paper17.EuclideanSupport
import Paper17.EuclideanCombination
import Paper17.LabelledApproximation
import Paper17.LoopModulus
import Paper17.HomotopyConsequences
import Paper17.NerveLabels
import Paper17.FiniteInterpolation
import Paper17.PositiveTime
import Paper17.LatticeResolution
import Paper17.SimplicialResolution
import Paper17.SimplicialFanResolution
import Paper17.ProjectiveStellarStep
import Paper17.IntegralHalfspacePresentation
import Paper17.FanCompatibleApproximation
import Paper17.Polytope
import Paper17.Delzant
import Paper17.Extension
import Paper17.Dugundji
import Paper17.ContinuousApproximation
import Paper17.AbsExt
import Paper17.AbsoluteRetract
import Paper17.Example24
import Paper17.Example24Geometry
import Paper17.Spheres
import Paper17.MetricCompare
import Paper17.MetricLower
import Paper17.MetricEquivalence
import Paper17.Approximation
import Paper17.HomotopyDensity

/-!
# The space of Delzant polytopes is an absolute retract

The core fixed contracts are proved and the full dependency axiom audit passes.
Additional source geometry and Appendix A are tracked in coverage.json. Main entry points:

* `Paper17.IsAbsoluteExtensor` / `IsAbsoluteRetract` — Definition 1.1
* `Paper17.theorem_3_1` — Theorem 3.1 (extension by refinement chains)
* `Paper17.theorem_1_2` — Theorem 1.2 (main theorem)
* `Paper17.corollary_1_3` — Corollary 1.3 (strong deformation retraction)
* `Paper17.DelzantPolytope.lemma_2_1` — Lemma 2.1 (interpolation along a chain)
* `Paper17.DelzantPolytope.lemma_2_3` — Lemma 2.3 (common refinements close to a target)
* `Paper17.hausdorffDist_twoTerm_le` — equation (2.2)
* Full controlled approximation and homotopy density are proved in Verification.Solution.
-/
