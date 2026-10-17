import Paper18.Category.PointedRigid
import Paper18.Category.PointedSkeleton
import Paper18.Category.FusionCategory

noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory

namespace Paper18.Category.PointedVec

variable (A : Type) [Fintype A] [AddGroup A]

/-- The convolution unit is the actual complex line in degree zero. -/
def unitSimpleIso : 𝟙_ (PointedVec A) ≅ simpleObject A 0 := Iso.refl _

instance simple_unit : Simple (𝟙_ (PointedVec A)) := by
  letI := simple_simpleObject (A := A) (0 : A)
  exact Simple.of_iso (unitSimpleIso A)

/-- The fusion rules are obtained from the actual convolution category and
its homogeneous-line skeleton. -/
def fusionRules : Paper18.FusionRules A := (skeleton A).fusionRules

/-- Positive FP dimensions exist for this actual category by the general
positive-matrix theorem applied to its categorical fusion coefficients. -/
def fusionBasis : Paper18.FusionBasis A := (skeleton A).fusionBasis

end Paper18.Category.PointedVec
