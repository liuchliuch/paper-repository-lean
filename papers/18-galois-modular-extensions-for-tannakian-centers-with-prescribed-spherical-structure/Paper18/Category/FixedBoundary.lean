import Paper18.Category.FixedBoundaryScalarTrivialization
import Paper18.Category.FixedBoundaryEquivariantBoundaryMonoidal
import Paper18.Category.FixedBoundaryModuleAutoequivalence
import Paper18.Category.FixedBoundaryNeutral
import Paper18.Category.FixedBoundaryModuleGrading
import Paper18.Category.FixedBoundaryRestrictBoundary
import Paper18.Category.FixedBoundaryModuleWattsEquivalence
import Paper18.Category.FixedBoundaryModuleAutoScalar
import Paper18.Category.FixedBoundaryModuleUnitTrivialization
import Paper18.Category.FixedBoundaryModuleGeneralWatts
import Paper18.Category.FixedBoundaryOddFunctorScalar
import Paper18.Category.FixedBoundaryOrdinaryExtraction
import Paper18.Category.FixedBoundaryModuleGradingTransport
import Paper18.Category.FixedBoundaryModuleImage
import Paper18.Category.FixedBoundaryNeutralNondegenerate
import Paper18.Category.FixedBoundaryNeutralComparison
import Paper18.Category.FixedBoundaryOddBoundaryModules
import Paper18.Category.FixedBoundaryOddRepresentation
import Paper18.Category.FixedBoundaryOddInvertible
import Paper18.Category.FixedBoundaryHomogeneousNaturality
import Paper18.Category.FixedBoundaryLocalCrossing
import Paper18.Category.FixedBoundaryNeutralAction
import Paper18.Category.FixedBoundaryCrossedMonodromy
import Paper18.Category.FixedBoundaryCrossedFunctor
import Paper18.Category.FixedBoundaryDescentComparison
import Paper18.Category.FixedBoundaryMinimalSpherical

/-!
# Actual categorical infrastructure for the fixed-boundary Lemma A.1

This entry point supplies actual boundary pairs and their groupoid, actual
internal-module equivalences retaining the specified boundary, coherent
monoidal regular actions and their transport to actual equivariantizations,
and genuine homogeneous decompositions. Native module functors out of
the regular module are represented by their actual unit values; module
automorphisms of actual homogeneous components have unique scalar
coordinates. The actual neutral category is braided equivalent to boundary modules,
so its nondegeneracy follows from the actual Tannakian de-equivariantization.
The specified comparison extends monoidally to that entire neutral category
and respects actual algebra translations. The arbitrary odd restriction
has a derived actual alpha-induction representative. Actual comparisons
on the two sign components glue to an ordinary ambient natural isomorphism
retaining the specified boundary.
A normalized scalar tensorator
defect is trivialized by an actual monoidal natural isomorphism with the
prescribed boundary components.

`FixedBoundary.minimalBoundary_trivializable` proves the entire universal
specified-boundary assertion for every actual minimal extension. Actual
odd alpha-induction representability, genuine crossed compatibility,
transparency and unit reduction, scalar tensorator extraction, H²
correction, and invariant regular descent are proved internally. The
lifted natural isomorphism is monoidal and retains every original alpha
component. `spherical_extension_of_c2_minimal` applies this result to the
actual double-dual boundary pair and constructs the prescribed spherical
structure on every actual minimal extension.

`LemmaA1Statement` additionally asks for existence of an actual minimal
extension. That existence assertion still requires the actual
crossed-extension/Picard realization argument and is not proved here.
-/
