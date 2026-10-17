import Paper18.Category.PositiveMonoidalFunctor
import Paper18.Category.EquivariantPivotal
import Paper18.Category.EquivariantIntegrality

/-! # Actual positivity of the pivotal equivariantization

The actual equivariant pivotal structure forgets pivotally to the ambient
positive category. A nonzero equivariant object has nonzero underlying
object, so its actual pivotal dimension is a positive FP dimension.
-/
noncomputable section
open CategoryTheory CategoryTheory.Category CategoryTheory.MonoidalCategory
open CategoryTheory.Limits
universe v u w t
namespace Paper18.Category.WeakAction
attribute [local instance 2000] RightRigidCategory.rightDual
variable {G : Type w} [Group G] [Fintype G]
  {C : Type u} [Category.{v} C] [Preadditive C] [Linear ℂ C]
  [HasKernels C] [HasFiniteBiproducts C]
  [∀ X Y : C, FiniteDimensional ℂ (X ⟶ Y)]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalLinear ℂ C]
  [RightRigidCategory C] [Simple (𝟙_ C)]
  (A : WeakAction G C)
  [∀ g : G, (A.ρ g).Additive] [∀ g : G, (A.ρ g).Linear ℂ]
  [∀ g : G, (A.ρ g).Monoidal] [A.IsMonoidal]
  {ι : Type t} [Fintype ι] (S : FiniteSemisimpleSkeleton C ι)
  (J : PivotalStructure C) (hJ : ∀ g : G, PreservesPivotal (A.ρ g) J J)

include S in
/-- Positivity of the actual ambient pivotal trace gives positivity of the
constructed actual equivariant pivotal trace on every categorical simple. -/
theorem Equivariant.pivotalStructure_positive (pJ : J.Positive) :
    (pivotalStructure A J hJ).Positive :=
  positive_of_faithful_pivotal A.forget (pivotalStructure A J hJ) J S
    (forget_preservesPivotal A J hJ) pJ

include S

/-- Positive pivotal uniqueness derives compatibility with every actual
translating equivalence of the weak action. -/
theorem rho_preservesPositivePivotal (pJ : J.Positive) (g : G) :
    PreservesPivotal (A.ρ g) J J :=
  preservesPivotal_of_positive_equivalence (A.ρ g) J J S S pJ pJ

/-- The actual pivotal structure on a finite monoidal equivariantization
of a positive pivotal fusion category. Compatibility with the action is
derived from positivity rather than supplied as additional data. -/
def positivePivotal (pJ : J.Positive) : PivotalStructure A.Equivariant :=
  Equivariant.pivotalStructure A J (rho_preservesPositivePivotal A S J pJ)

/-- The constructed actual equivariant pivotal structure has positive
categorical trace on every actual simple. -/
theorem positivePivotal_positive (pJ : J.Positive) : (positivePivotal A S J pJ).Positive :=
  Equivariant.pivotalStructure_positive A S J (rho_preservesPositivePivotal A S J pJ) pJ

/-- Its actual sphericality follows on all endomorphisms. -/
theorem positivePivotal_spherical (pJ : J.Positive) : (positivePivotal A S J pJ).Spherical :=
  Equivariant.pivotalStructure_spherical A J (rho_preservesPositivePivotal A S J pJ)
    (J.spherical_of_positive S pJ)

/-- The canonical actual forgetful functor preserves this positive pivotal
structure using its canonical chosen-dual comparison. -/
theorem positivePivotal_forget_preserves (pJ : J.Positive) :
    PreservesPivotal A.forget (positivePivotal A S J pJ) J :=
  forget_preservesPivotal A J (rho_preservesPositivePivotal A S J pJ)

end Paper18.Category.WeakAction
