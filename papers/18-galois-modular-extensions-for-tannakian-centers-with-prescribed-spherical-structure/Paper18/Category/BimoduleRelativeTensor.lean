import Paper18.Category.BimoduleRelativeTensorFusion
import Paper18.Category.BimoduleRelativeTensorFreeHom
import Paper18.Category.BimoduleRelativeTensorWattsLinear
import Paper18.Category.BimoduleRelativeTensorFunctorCompositionCoherence
import Paper18.Category.BimoduleRelativeTensorMoritaEquivalence
import Paper18.Category.BimoduleRelativeTensorBlockOrbit
import Paper18.Category.BimoduleRelativeTensorSplitBarNatural
import Paper18.Category.BimoduleRelativeTensorFunctorDescent
import Paper18.Category.BimoduleRelativeTensorFunctorDescentMap

/-! # Actual native bimodule relative composition

Arbitrary actual algebra objects and their actual native bimodules form
the proved bicategory of balancing coequalizers. Its associator, unitors,
pentagon and triangle are actual morphisms and equations. A separable
middle algebra supplies an actual split coequalizer.

The actual relative tensor functor is complex linear and strong for the
native ambient action. Its evaluation at the regular algebra recovers
the given bimodule, completing the actual Eilenberg--Watts equivalence
for separable algebras. Actual free bimodule Hom coordinates are derived
from the two native free-module universal properties.

The actual relative tensor representation is a complex linear strong
monoidal equivalence to the monoidal opposite of genuine ambient-module
endofunctors. Its tensor and unit comparisons are the actual quotient
associator and action contractions, and all coherence follows from the
proved bimodule pentagon and triangle.
-/
